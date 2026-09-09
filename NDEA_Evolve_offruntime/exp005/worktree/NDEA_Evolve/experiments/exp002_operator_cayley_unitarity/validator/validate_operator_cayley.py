#!/usr/bin/env python3
"""Strict independent validator for the Exp002 exact matrix certificate.

This validator does not establish the universal Lean theorems.  It independently
reconstructs every finite Gaussian-rational claim carried by the Julia certificate
and applies a separately fixed gate to the numerical run receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from fractions import Fraction
from pathlib import Path


CERT_SCHEMA = "ndea.exp002.operator_cayley_certificate.v1"
CORE_SCHEMA = "ndea.exp002.operator_cayley_core.v1"
RECEIPT_SCHEMA = "ndea.exp002.operator_cayley_run_receipt.v1"
FIXED_NUMERIC_LIMIT = Decimal("1e-10")
INT_RE = re.compile(r"(?:0|-[1-9][0-9]*|[1-9][0-9]*)\Z")
POS_RE = re.compile(r"[1-9][0-9]*\Z")
HEX64_RE = re.compile(r"[0-9a-f]{64}\Z")


class ValidationError(Exception):
    pass


CHECKS: list[str] = []


def ensure(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def checked(label: str, condition: bool, message: str | None = None) -> None:
    ensure(condition, message or label)
    CHECKS.append(label)


def exact_keys(value: object, keys: set[str], where: str) -> dict:
    ensure(isinstance(value, dict), f"{where}: expected object")
    actual = set(value)
    ensure(actual == keys, f"{where}: key set mismatch; missing={sorted(keys-actual)} extra={sorted(actual-keys)}")
    return value


def no_duplicate_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValidationError(f"duplicate JSON key: {key!r}")
        out[key] = value
    return out


def reject_float(token: str):
    raise ValidationError(f"floating JSON number forbidden in exact certificate: {token}")


def load_json(path: Path, exact: bool = True):
    try:
        with path.open("r", encoding="utf-8") as stream:
            return json.load(
                stream,
                object_pairs_hook=no_duplicate_object,
                parse_float=reject_float if exact else float,
                parse_constant=lambda token: (_ for _ in ()).throw(
                    ValidationError(f"non-finite JSON constant forbidden: {token}")),
            )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValidationError(f"cannot parse {path}: {exc}") from exc


def canonical_bytes(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                h.update(block)
    except OSError as exc:
        raise ValidationError(f"cannot hash {path}: {exc}") from exc
    return h.hexdigest()


@dataclass(frozen=True)
class G:
    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    def __add__(self, other: "G") -> "G":
        return G(self.re + other.re, self.im + other.im)

    def __sub__(self, other: "G") -> "G":
        return G(self.re - other.re, self.im - other.im)

    def __neg__(self) -> "G":
        return G(-self.re, -self.im)

    def __mul__(self, other: "G") -> "G":
        return G(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    def __truediv__(self, other: "G") -> "G":
        ensure(other != ZERO, "division by zero in certificate reconstruction")
        denominator = other.re * other.re + other.im * other.im
        return G((self.re * other.re + self.im * other.im) / denominator,
                 (self.im * other.re - self.re * other.im) / denominator)

    def conj(self) -> "G":
        return G(self.re, -self.im)


ZERO = G()
ONE = G(Fraction(1), Fraction(0))
I = G(Fraction(0), Fraction(1))


def parse_rat(value, where: str) -> Fraction:
    obj = exact_keys(value, {"num", "den"}, where)
    num, den = obj["num"], obj["den"]
    ensure(isinstance(num, str) and INT_RE.fullmatch(num), f"{where}.num: noncanonical integer string")
    ensure(isinstance(den, str) and POS_RE.fullmatch(den), f"{where}.den: noncanonical positive denominator")
    result = Fraction(int(num), int(den))
    ensure(str(result.numerator) == num and str(result.denominator) == den,
           f"{where}: rational must be normalized")
    return result


def parse_g(value, where: str) -> G:
    obj = exact_keys(value, {"re", "im"}, where)
    return G(parse_rat(obj["re"], where + ".re"), parse_rat(obj["im"], where + ".im"))


def rat_json(value: Fraction):
    return {"num": str(value.numerator), "den": str(value.denominator)}


def g_json(value: G):
    return {"re": rat_json(value.re), "im": rat_json(value.im)}


Matrix = tuple[tuple[G, ...], ...]
Vector = tuple[G, ...]


def parse_matrix(value, where: str, rows: int | None = None, cols: int | None = None) -> Matrix:
    ensure(isinstance(value, list) and value, f"{where}: expected nonempty matrix array")
    ensure(all(isinstance(row, list) and row for row in value), f"{where}: expected nonempty rows")
    width = len(value[0])
    ensure(all(len(row) == width for row in value), f"{where}: ragged matrix")
    if rows is not None:
        ensure(len(value) == rows, f"{where}: wrong row count")
    if cols is not None:
        ensure(width == cols, f"{where}: wrong column count")
    return tuple(tuple(parse_g(cell, f"{where}[{i}][{j}]") for j, cell in enumerate(row))
                 for i, row in enumerate(value))


def parse_vector(value, where: str, length: int | None = None) -> Vector:
    ensure(isinstance(value, list), f"{where}: expected vector array")
    if length is not None:
        ensure(len(value) == length, f"{where}: wrong vector length")
    return tuple(parse_g(cell, f"{where}[{i}]") for i, cell in enumerate(value))


def matrix_json(a: Matrix):
    return [[g_json(cell) for cell in row] for row in a]


def shape(a: Matrix) -> tuple[int, int]:
    return len(a), len(a[0])


def zero_matrix(rows: int, cols: int) -> Matrix:
    return tuple(tuple(ZERO for _ in range(cols)) for _ in range(rows))


def eye(n: int) -> Matrix:
    return tuple(tuple(ONE if i == j else ZERO for j in range(n)) for i in range(n))


def madd(a: Matrix, b: Matrix) -> Matrix:
    ensure(shape(a) == shape(b), "matrix addition dimension mismatch")
    return tuple(tuple(x + y for x, y in zip(arow, brow)) for arow, brow in zip(a, b))


def mneg(a: Matrix) -> Matrix:
    return tuple(tuple(-x for x in row) for row in a)


def msub(a: Matrix, b: Matrix) -> Matrix:
    return madd(a, mneg(b))


def mscale(c: G, a: Matrix) -> Matrix:
    return tuple(tuple(c * x for x in row) for row in a)


def mmul(a: Matrix, b: Matrix) -> Matrix:
    ar, ac = shape(a)
    br, bc = shape(b)
    ensure(ac == br, "matrix multiplication dimension mismatch")
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(ac)), ZERO)
                       for j in range(bc)) for i in range(ar))


def dagger(a: Matrix) -> Matrix:
    rows, cols = shape(a)
    return tuple(tuple(a[j][i].conj() for j in range(rows)) for i in range(cols))


def comm(a: Matrix, b: Matrix) -> Matrix:
    return msub(mmul(a, b), mmul(b, a))


def is_zero(a: Matrix) -> bool:
    return all(cell == ZERO for row in a for cell in row)


def is_hermitian(a: Matrix) -> bool:
    return shape(a)[0] == shape(a)[1] and a == dagger(a)


def apply_matrix(a: Matrix, x: Vector) -> Vector:
    rows, cols = shape(a)
    ensure(cols == len(x), "matrix-vector dimension mismatch")
    return tuple(sum((a[i][j] * x[j] for j in range(cols)), ZERO) for i in range(rows))


def inner(x: Vector, y: Vector) -> G:
    ensure(len(x) == len(y), "inner-product dimension mismatch")
    return sum((a.conj() * b for a, b in zip(x, y)), ZERO)


def determinant_with_trace(a: Matrix):
    n, m = shape(a)
    ensure(n == m, "determinant requires square matrix")
    work = [list(row) for row in a]
    det = ONE
    swaps = 0
    pivots = []
    for col in range(n):
        pivot_row = next((row for row in range(col, n) if work[row][col] != ZERO), None)
        if pivot_row is None:
            pivots.append({"column": col + 1, "status": "ZERO_COLUMN"})
            return ZERO, {"row_swaps": swaps, "pivots": pivots, "singular": True}
        if pivot_row != col:
            work[col], work[pivot_row] = work[pivot_row], work[col]
            swaps += 1
        pivot = work[col][col]
        det = det * pivot
        pivots.append({"column": col + 1, "selected_row": pivot_row + 1,
                       "swapped": pivot_row != col, "pivot": g_json(pivot)})
        for row in range(col + 1, n):
            if work[row][col] != ZERO:
                factor = work[row][col] / pivot
                for j in range(col, n):
                    work[row][j] = work[row][j] - factor * work[col][j]
    if swaps % 2:
        det = -det
    return det, {"row_swaps": swaps, "pivots": pivots, "singular": False}


def inverse_with_trace(a: Matrix):
    n, m = shape(a)
    ensure(n == m, "inverse requires square matrix")
    ident = eye(n)
    aug = [list(a[i] + ident[i]) for i in range(n)]
    trace = []
    for col in range(n):
        pivot_row = next((row for row in range(col, n) if aug[row][col] != ZERO), None)
        if pivot_row is None:
            trace.append({"operation": "singular", "column": col + 1})
            return None, trace
        if pivot_row != col:
            aug[col], aug[pivot_row] = aug[pivot_row], aug[col]
            trace.append({"operation": "swap", "row_a": col + 1, "row_b": pivot_row + 1})
        pivot = aug[col][col]
        trace.append({"operation": "scale", "row": col + 1, "divisor": g_json(pivot)})
        aug[col] = [value / pivot for value in aug[col]]
        for row in range(n):
            if row == col:
                continue
            factor = aug[row][col]
            if factor != ZERO:
                trace.append({"operation": "eliminate", "source_row": col + 1,
                              "target_row": row + 1, "factor": g_json(factor)})
                aug[row] = [aug[row][j] - factor * aug[col][j] for j in range(2 * n)]
    return tuple(tuple(row[n:]) for row in aug), trace


INSTANCE_KEYS = {
    "dimension", "a", "H", "D", "N", "D_inverse", "U", "det_D", "det_N",
    "det_U", "det_U_modulus_sq", "pivot_trace_D_inverse", "determinant_traces",
    "gram_target", "residuals",
}
RESIDUAL_KEYS = {
    "hermitian", "D_dagger_minus_N", "N_dagger_minus_D", "D_N_commutator",
    "Dinv_left", "Dinv_right", "update_DU_minus_N", "Ddagger_D_minus_gram",
    "Ndagger_N_minus_gram", "Udagger_U_minus_I", "U_Udagger_minus_I",
}


def verify_cayley_record(record, where: str, *, has_id: bool, require_hermitian: bool):
    keys = INSTANCE_KEYS | ({"id"} if has_id else set())
    obj = exact_keys(record, keys, where)
    n = obj["dimension"]
    ensure(type(n) is int and 1 <= n <= 32, f"{where}.dimension: invalid")
    if has_id:
        ensure(isinstance(obj["id"], str) and obj["id"], f"{where}.id: invalid")
    a = parse_rat(obj["a"], where + ".a")
    h = parse_matrix(obj["H"], where + ".H", n, n)
    d = parse_matrix(obj["D"], where + ".D", n, n)
    numerator = parse_matrix(obj["N"], where + ".N", n, n)
    dinv = parse_matrix(obj["D_inverse"], where + ".D_inverse", n, n)
    u = parse_matrix(obj["U"], where + ".U", n, n)
    ident = eye(n)
    iah = mscale(I * G(a), h)
    expected_d = madd(ident, iah)
    expected_n = msub(ident, iah)
    checked(where + ".D", d == expected_d)
    checked(where + ".N", numerator == expected_n)
    expected_inv, inv_trace = inverse_with_trace(d)
    checked(where + ".nonsingular", expected_inv is not None)
    checked(where + ".D_inverse", dinv == expected_inv)
    checked(where + ".inverse_trace", obj["pivot_trace_D_inverse"] == inv_trace)
    checked(where + ".U", u == mmul(numerator, dinv))
    h2 = mmul(h, h)
    gram = madd(ident, mscale(G(a * a), h2))
    checked(where + ".gram_target", parse_matrix(obj["gram_target"], where + ".gram_target", n, n) == gram)
    residuals = {
        "hermitian": msub(dagger(h), h),
        "D_dagger_minus_N": msub(dagger(d), numerator),
        "N_dagger_minus_D": msub(dagger(numerator), d),
        "D_N_commutator": comm(d, numerator),
        "Dinv_left": msub(mmul(dinv, d), ident),
        "Dinv_right": msub(mmul(d, dinv), ident),
        "update_DU_minus_N": msub(mmul(d, u), numerator),
        "Ddagger_D_minus_gram": msub(mmul(dagger(d), d), gram),
        "Ndagger_N_minus_gram": msub(mmul(dagger(numerator), numerator), gram),
        "Udagger_U_minus_I": msub(mmul(dagger(u), u), ident),
        "U_Udagger_minus_I": msub(mmul(u, dagger(u)), ident),
    }
    residual_obj = exact_keys(obj["residuals"], RESIDUAL_KEYS, where + ".residuals")
    for name, value in residuals.items():
        checked(where + ".residuals." + name,
                parse_matrix(residual_obj[name], where + ".residuals." + name, n, n) == value)
    if require_hermitian:
        checked(where + ".Hermitian", is_hermitian(h))
        for name in RESIDUAL_KEYS:
            checked(where + ".zero." + name, is_zero(residuals[name]))
    else:
        checked(where + ".nonHermitian", not is_hermitian(h))
        for name in ("D_N_commutator", "Dinv_left", "Dinv_right", "update_DU_minus_N"):
            checked(where + ".structural_zero." + name, is_zero(residuals[name]))
    determinant_traces = exact_keys(obj["determinant_traces"], {"D", "N", "U"}, where + ".determinant_traces")
    for name, matrix, field in (("D", d, "det_D"), ("N", numerator, "det_N"), ("U", u, "det_U")):
        det, trace = determinant_with_trace(matrix)
        checked(where + "." + field, parse_g(obj[field], where + "." + field) == det)
        checked(where + ".determinant_trace." + name, determinant_traces[name] == trace)
    det_u = parse_g(obj["det_U"], where + ".det_U")
    checked(where + ".det_U_modulus_sq",
            parse_g(obj["det_U_modulus_sq"], where + ".det_U_modulus_sq") == det_u.conj() * det_u)
    return {"n": n, "a": a, "H": h, "D": d, "N": numerator, "Dinv": dinv, "U": u,
            "residuals": residuals}


def parse_poly(value, where: str):
    ensure(isinstance(value, list), f"{where}: polynomial must be an array")
    out = {}
    previous = None
    for index, term in enumerate(value):
        obj = exact_keys(term, {"a_power", "H_power", "coefficient"}, f"{where}[{index}]")
        ap, hp = obj["a_power"], obj["H_power"]
        ensure(type(ap) is int and type(hp) is int and ap >= 0 and hp >= 0,
               f"{where}[{index}]: invalid powers")
        key = (ap, hp)
        ensure(key not in out and (previous is None or previous < key), f"{where}: terms not strictly sorted/unique")
        out[key] = parse_g(obj["coefficient"], f"{where}[{index}].coefficient")
        ensure(out[key] != ZERO, f"{where}: zero coefficient forbidden")
        previous = key
    return out


def poly_star(p):
    return {key: value.conj() for key, value in p.items()}


def poly_mul(p, q):
    out = {}
    for (ap, hp), x in p.items():
        for (aq, hq), y in q.items():
            key = (ap + aq, hp + hq)
            out[key] = out.get(key, ZERO) + x * y
    return {key: value for key, value in out.items() if value != ZERO}


def verify_symbolic(value):
    keys = {"variables", "X", "Y", "star_X", "star_Y", "star_X_equals_Y", "star_Y_equals_X",
            "Xstar_X", "Ystar_Y", "X_Y", "common_gram", "rewrite_trace"}
    obj = exact_keys(value, keys, "core.symbolic_star_polynomial_derivation")
    expected_variables = {"a": "central real scalar", "H": "self-adjoint noncommuting generator"}
    checked("symbolic.variables", obj["variables"] == expected_variables)
    expected_trace = [
        "conjugate i to -i while fixing real a and self-adjoint H",
        "multiply sparse coefficient maps by exact convolution",
        "cancel opposite degree-(1,1) coefficients",
        "obtain I+a^2*H^2",
    ]
    checked("symbolic.rewrite_trace", obj["rewrite_trace"] == expected_trace)
    x = parse_poly(obj["X"], "symbolic.X")
    y = parse_poly(obj["Y"], "symbolic.Y")
    sx = parse_poly(obj["star_X"], "symbolic.star_X")
    sy = parse_poly(obj["star_Y"], "symbolic.star_Y")
    gram = parse_poly(obj["common_gram"], "symbolic.common_gram")
    checked("symbolic.X", x == {(0, 0): ONE, (1, 1): I})
    checked("symbolic.Y", y == {(0, 0): ONE, (1, 1): -I})
    checked("symbolic.star_X", sx == poly_star(x) == y)
    checked("symbolic.star_Y", sy == poly_star(y) == x)
    checked("symbolic.star_flags", obj["star_X_equals_Y"] is True and obj["star_Y_equals_X"] is True)
    expected_gram = {(0, 0): ONE, (2, 2): ONE}
    checked("symbolic.common_gram", gram == expected_gram)
    checked("symbolic.Xstar_X", parse_poly(obj["Xstar_X"], "symbolic.Xstar_X") == poly_mul(sx, x) == gram)
    checked("symbolic.Ystar_Y", parse_poly(obj["Ystar_Y"], "symbolic.Ystar_Y") == poly_mul(sy, y) == gram)
    checked("symbolic.X_Y", parse_poly(obj["X_Y"], "symbolic.X_Y") == poly_mul(x, y) == gram)


def cayley_scalar_matrix(h: Matrix, a: Fraction):
    n, m = shape(h)
    ensure(n == m, "Cayley requires square matrix")
    d = madd(eye(n), mscale(I * G(a), h))
    numerator = msub(eye(n), mscale(I * G(a), h))
    inv, _ = inverse_with_trace(d)
    ensure(inv is not None, "unexpected singular denominator")
    return mmul(numerator, inv), d, inv


def verify_composition(core, instances):
    obj = exact_keys(core["composition"], {
        "factor_order", "P21", "P12", "P321", "P21_minus_P12",
        "P21_unitarity_left_residual", "P21_unitarity_right_residual",
        "P321_unitarity_left_residual", "P321_unitarity_right_residual", "formal_word_certificate",
    }, "core.composition")
    by_id = {item["id"]: item for item in instances}
    ensure(set(by_id) == {"pauli_X_half", "pauli_Z_two_thirds", "pauli_Y_negative_three_fifths"},
           "exact instance IDs mismatch")
    u1, u2, u3 = (by_id[name]["U"] for name in
                  ("pauli_X_half", "pauli_Z_two_thirds", "pauli_Y_negative_three_fifths"))
    p21, p12 = mmul(u2, u1), mmul(u1, u2)
    p321 = mmul(u3, p21)
    i2 = eye(2)
    fields = {
        "P21": p21, "P12": p12, "P321": p321, "P21_minus_P12": msub(p21, p12),
        "P21_unitarity_left_residual": msub(mmul(dagger(p21), p21), i2),
        "P21_unitarity_right_residual": msub(mmul(p21, dagger(p21)), i2),
        "P321_unitarity_left_residual": msub(mmul(dagger(p321), p321), i2),
        "P321_unitarity_right_residual": msub(mmul(p321, dagger(p321)), i2),
    }
    for field, expected in fields.items():
        checked("composition." + field, parse_matrix(obj[field], "composition." + field, 2, 2) == expected)
    checked("composition.noncommuting_order", not is_zero(fields["P21_minus_P12"]))
    for field in ("P21_unitarity_left_residual", "P21_unitarity_right_residual",
                  "P321_unitarity_left_residual", "P321_unitarity_right_residual"):
        checked("composition.zero." + field, is_zero(fields[field]))
    checked("composition.factor_order", obj["factor_order"] == [
        "pauli_Y_negative_three_fifths", "pauli_Z_two_thirds", "pauli_X_half"])
    expected_word = {
        "product_word": ["U3", "U2", "U1"],
        "adjoint_word": ["U1_dagger", "U2_dagger", "U3_dagger"],
        "Pdagger_P_word": ["U1_dagger", "U2_dagger", "U3_dagger", "U3", "U2", "U1"],
        "adjacent_cancellations": [
            {"pair": ["U3_dagger", "U3"], "remaining": ["U1_dagger", "U2_dagger", "U2", "U1"]},
            {"pair": ["U2_dagger", "U2"], "remaining": ["U1_dagger", "U1"]},
            {"pair": ["U1_dagger", "U1"], "remaining": ["I"]},
        ],
        "commutation_used": False,
    }
    checked("composition.formal_word_certificate", obj["formal_word_certificate"] == expected_word)
    return {"u1": u1, "u2": u2, "u3": u3, "p21": p21, "p12": p12, "p321": p321,
            "h1": by_id["pauli_X_half"]["H"], "h2": by_id["pauli_Z_two_thirds"]["H"],
            "r1": by_id["pauli_X_half"]["Dinv"], "r2": by_id["pauli_Z_two_thirds"]["Dinv"]}


def verify_vectors(value, composition):
    ensure(isinstance(value, list) and len(value) == 9, "exact_vector_norm_checks: expected 9 records")
    factors = {"U1": composition["u1"], "U2": composition["u2"], "P321": composition["p321"]}
    expected_factor_order = [name for name in ("U1", "U2", "P321") for _ in range(3)]
    seen = []
    expected_inputs = [
        (ONE, ZERO),
        (G(Fraction(1), Fraction(1)), G(Fraction(2, 3), Fraction(-1, 4))),
        (G(Fraction(-5, 7), Fraction(3, 8)), G(Fraction(11, 6), Fraction(2, 9))),
    ]
    for index, record in enumerate(value):
        obj = exact_keys(record, {"factor", "input", "output", "norm_sq_before", "norm_sq_after"},
                         f"exact_vector_norm_checks[{index}]")
        factor = obj["factor"]
        ensure(factor in factors, f"vector check {index}: unknown factor")
        seen.append(factor)
        x = parse_vector(obj["input"], f"vector[{index}].input", 2)
        checked(f"vector[{index}].input", x == expected_inputs[index % 3])
        y = parse_vector(obj["output"], f"vector[{index}].output", 2)
        expected_y = apply_matrix(factors[factor], x)
        checked(f"vector[{index}].output", y == expected_y)
        before, after = inner(x, x), inner(y, y)
        checked(f"vector[{index}].before", parse_g(obj["norm_sq_before"], f"vector[{index}].before") == before)
        checked(f"vector[{index}].after", parse_g(obj["norm_sq_after"], f"vector[{index}].after") == after)
        checked(f"vector[{index}].preserved", before == after)
    checked("vector.factor_order", seen == expected_factor_order)


def verify_order_defect(value, composition):
    obj = exact_keys(value, {"generator_commutator", "cayley_commutator", "factorized_rhs",
                            "equivalent_fully_reversed_rhs", "residual", "fully_reversed_residual",
                            "coefficient", "parameters_nonzero", "generator_commutes", "cayley_factors_commute"},
                     "core.order_defect")
    hcomm = comm(composition["h1"], composition["h2"])
    ucomm = comm(composition["u1"], composition["u2"])
    coefficient = parse_rat(obj["coefficient"], "order_defect.coefficient")
    checked("order_defect.coefficient", coefficient == Fraction(-4, 3))
    rhs = mscale(G(coefficient), mmul(mmul(mmul(mmul(composition["r1"], composition["r2"]), hcomm),
                                                composition["r2"]), composition["r1"]))
    reversed_rhs = mscale(G(coefficient), mmul(mmul(mmul(mmul(composition["r2"], composition["r1"]), hcomm),
                                                         composition["r1"]), composition["r2"]))
    fields = {
        "generator_commutator": hcomm, "cayley_commutator": ucomm, "factorized_rhs": rhs,
        "equivalent_fully_reversed_rhs": reversed_rhs, "residual": msub(ucomm, rhs),
        "fully_reversed_residual": msub(ucomm, reversed_rhs),
    }
    for field, expected in fields.items():
        checked("order_defect." + field, parse_matrix(obj[field], "order_defect." + field, 2, 2) == expected)
    checked("order_defect.identity", is_zero(fields["residual"]))
    checked("order_defect.reversed_identity", is_zero(fields["fully_reversed_residual"]))
    checked("order_defect.flags", obj["parameters_nonzero"] is True and
            obj["generator_commutes"] is False and obj["cayley_factors_commute"] is False)
    checked("order_defect.nonzero", not is_zero(hcomm) and not is_zero(ucomm))
    return {"hcomm": hcomm, "ucomm": ucomm, "rhs": rhs}


def verify_search(value):
    obj = exact_keys(value, {"domain", "total", "invertible_denominator", "singular_denominator",
                            "nonhermitian_invertible", "nonhermitian_nonunitary", "first_singular",
                            "first_nonhermitian_nonunitary"}, "core.exhaustive_counterexample_search")
    checked("search.domain", obj["domain"] ==
            "2x2 real matrices, row-major entries in {-1,0,1}, nested lexicographic loops; a=1")
    counts = {"total": 0, "invertible_denominator": 0, "singular_denominator": 0,
              "nonhermitian_invertible": 0, "nonhermitian_nonunitary": 0}
    first_singular = None
    first_nonunitary = None
    i2 = eye(2)
    for a11 in range(-1, 2):
        for a12 in range(-1, 2):
            for a21 in range(-1, 2):
                for a22 in range(-1, 2):
                    counts["total"] += 1
                    h = ((G(Fraction(a11)), G(Fraction(a12))),
                         (G(Fraction(a21)), G(Fraction(a22))))
                    d = madd(i2, mscale(I, h))
                    dinv, _ = inverse_with_trace(d)
                    if dinv is None:
                        counts["singular_denominator"] += 1
                        if first_singular is None:
                            first_singular = {"H": matrix_json(h), "D": matrix_json(d)}
                        continue
                    counts["invertible_denominator"] += 1
                    u = mmul(msub(i2, mscale(I, h)), dinv)
                    defect = msub(mmul(dagger(u), u), i2)
                    if not is_hermitian(h):
                        counts["nonhermitian_invertible"] += 1
                        if not is_zero(defect):
                            counts["nonhermitian_nonunitary"] += 1
                            if first_nonunitary is None:
                                first_nonunitary = {"H": matrix_json(h), "D": matrix_json(d),
                                                    "U": matrix_json(u), "unitarity_defect": matrix_json(defect)}
    for name, expected in counts.items():
        checked("search." + name, type(obj[name]) is int and obj[name] == expected)
    checked("search.first_singular", obj["first_singular"] == first_singular)
    checked("search.first_nonhermitian_nonunitary", obj["first_nonhermitian_nonunitary"] == first_nonunitary)


def verify_adversarial(value, composition, order):
    ensure(isinstance(value, list), "adversarial_witnesses: expected array")
    expected_ids = [
        "drop_hermitian", "complex_step_nonunitary", "complex_step_singular", "omit_i",
        "mismatched_steps", "false_cayley_semigroup_merging", "false_order_independence",
        "wrong_order_defect_sign", "wrong_left_inverse_order", "zero_parameter_breaks_commutation_iff",
        "sign_reversal_is_adjoint_not_instability",
    ]
    ensure([item.get("id") if isinstance(item, dict) else None for item in value] == expected_ids,
           "adversarial witness IDs/order mismatch")
    w = {item["id"]: item for item in value}
    for name in expected_ids[:-1]:
        checked("adversarial.classification." + name, w[name].get("classification") == "EXACT_COUNTEREXAMPLE")
    checked("adversarial.classification.nuance", w[expected_ids[-1]].get("classification") == "EXACT_NUANCE")

    drop = exact_keys(w["drop_hermitian"], {"id", "classification", "record", "unitarity_defect"}, "adversarial.drop")
    drop_rec = verify_cayley_record(drop["record"], "adversarial.drop.record", has_id=False, require_hermitian=False)
    defect = msub(mmul(dagger(drop_rec["U"]), drop_rec["U"]), eye(drop_rec["n"]))
    checked("adversarial.drop.defect", parse_matrix(drop["unitarity_defect"], "adversarial.drop.defect", 2, 2) == defect)
    checked("adversarial.drop.nonzero", not is_zero(defect))

    nonunit = exact_keys(w["complex_step_nonunitary"], {"id", "classification", "record"}, "adversarial.complex_nonunitary")["record"]
    exact_keys(nonunit, {"alpha", "D", "N", "U", "modulus_sq_minus_one", "singular", "pivot_trace"}, "complex_nonunitary.record")
    alpha = parse_g(nonunit["alpha"], "complex_nonunitary.alpha")
    d = ((ONE + I * alpha,),)
    nmat = ((ONE - I * alpha,),)
    inv, trace = inverse_with_trace(d)
    ensure(inv is not None, "complex nonunitary fixture unexpectedly singular")
    u = mmul(nmat, inv)
    checked("adversarial.complex_nonunitary.alpha", alpha == G(Fraction(0), Fraction(1, 2)))
    checked("adversarial.complex_nonunitary.D", parse_matrix(nonunit["D"], "complex_nonunitary.D", 1, 1) == d)
    checked("adversarial.complex_nonunitary.N", parse_matrix(nonunit["N"], "complex_nonunitary.N", 1, 1) == nmat)
    checked("adversarial.complex_nonunitary.U", parse_matrix(nonunit["U"], "complex_nonunitary.U", 1, 1) == u)
    checked("adversarial.complex_nonunitary.trace", nonunit["pivot_trace"] == trace and nonunit["singular"] is False)
    moddef = u[0][0].conj() * u[0][0] - ONE
    checked("adversarial.complex_nonunitary.defect", parse_g(nonunit["modulus_sq_minus_one"], "complex_nonunitary.defect") == moddef != ZERO)

    singular = exact_keys(w["complex_step_singular"], {"id", "classification", "record"}, "adversarial.complex_singular")["record"]
    exact_keys(singular, {"alpha", "D", "singular", "pivot_trace"}, "complex_singular.record")
    salpha = parse_g(singular["alpha"], "complex_singular.alpha")
    sd = ((ONE + I * salpha,),)
    sinv, strace = inverse_with_trace(sd)
    checked("adversarial.complex_singular.alpha", salpha == I)
    checked("adversarial.complex_singular.D", parse_matrix(singular["D"], "complex_singular.D", 1, 1) == sd)
    checked("adversarial.complex_singular", sinv is None and singular["singular"] is True and singular["pivot_trace"] == strace)

    omit = exact_keys(w["omit_i"], {"id", "classification", "U", "modulus_sq_minus_one"}, "adversarial.omit_i")
    omit_u = parse_g(omit["U"], "omit_i.U")
    checked("adversarial.omit_i.U", omit_u == G(Fraction(1, 3)))
    checked("adversarial.omit_i.defect", parse_g(omit["modulus_sq_minus_one"], "omit_i.defect") == omit_u.conj() * omit_u - ONE != ZERO)

    mismatch = exact_keys(w["mismatched_steps"], {"id", "classification", "denominator_a", "numerator_b", "U", "modulus_sq_minus_one"}, "adversarial.mismatch")
    da = parse_rat(mismatch["denominator_a"], "mismatch.denominator_a")
    nb = parse_rat(mismatch["numerator_b"], "mismatch.numerator_b")
    mismatch_u = (ONE - I * G(nb)) / (ONE + I * G(da))
    checked("adversarial.mismatch.U", parse_g(mismatch["U"], "mismatch.U") == mismatch_u)
    checked("adversarial.mismatch.defect", parse_g(mismatch["modulus_sq_minus_one"], "mismatch.defect") == mismatch_u.conj() * mismatch_u - ONE != ZERO)

    semi = exact_keys(w["false_cayley_semigroup_merging"], {"id", "classification", "generator", "a", "b", "C_a", "C_b", "C_a_times_C_b", "C_a_plus_b", "residual"}, "adversarial.semigroup")
    h = parse_matrix(semi["generator"], "semigroup.generator", 1, 1)
    a, b = parse_rat(semi["a"], "semigroup.a"), parse_rat(semi["b"], "semigroup.b")
    ca, _, _ = cayley_scalar_matrix(h, a)
    cb, _, _ = cayley_scalar_matrix(h, b)
    cab, _, _ = cayley_scalar_matrix(h, a + b)
    product, residual = mmul(ca, cb), msub(mmul(ca, cb), cab)
    for field, expected in (("C_a", ca), ("C_b", cb), ("C_a_times_C_b", product), ("C_a_plus_b", cab), ("residual", residual)):
        checked("adversarial.semigroup." + field, parse_matrix(semi[field], "semigroup." + field, 1, 1) == expected)
    checked("adversarial.semigroup.false", not is_zero(residual))

    order_ind = exact_keys(w["false_order_independence"], {"id", "classification", "P21_minus_P12"}, "adversarial.order_independence")
    delta = msub(composition["p21"], composition["p12"])
    checked("adversarial.order_independence", parse_matrix(order_ind["P21_minus_P12"], "order_independence.delta", 2, 2) == delta and not is_zero(delta))

    wrong_sign = exact_keys(w["wrong_order_defect_sign"], {"id", "classification", "wrong_rhs", "residual"}, "adversarial.wrong_sign")
    wrong_rhs = mneg(order["rhs"])
    wrong_residual = msub(order["ucomm"], wrong_rhs)
    checked("adversarial.wrong_sign.rhs", parse_matrix(wrong_sign["wrong_rhs"], "wrong_sign.rhs", 2, 2) == wrong_rhs)
    checked("adversarial.wrong_sign.residual", parse_matrix(wrong_sign["residual"], "wrong_sign.residual", 2, 2) == wrong_residual and not is_zero(wrong_residual))

    wrong_left = exact_keys(w["wrong_left_inverse_order"], {"id", "classification", "description", "wrong_rhs", "residual"}, "adversarial.wrong_left")
    checked("adversarial.wrong_left.description", wrong_left["description"] == "left inverse pair swapped while right pair is unchanged")
    coefficient = G(Fraction(-4, 3))
    wrong_left_rhs = mscale(coefficient, mmul(mmul(mmul(mmul(composition["r2"], composition["r1"]), order["hcomm"]), composition["r2"]), composition["r1"]))
    wrong_left_residual = msub(order["ucomm"], wrong_left_rhs)
    checked("adversarial.wrong_left.rhs", parse_matrix(wrong_left["wrong_rhs"], "wrong_left.rhs", 2, 2) == wrong_left_rhs)
    checked("adversarial.wrong_left.residual", parse_matrix(wrong_left["residual"], "wrong_left.residual", 2, 2) == wrong_left_residual and not is_zero(wrong_left_residual))

    zero_step = exact_keys(w["zero_parameter_breaks_commutation_iff"], {"id", "classification", "a", "generator_commutator", "C_zero", "C_zero_commutator_with_U2"}, "adversarial.zero_step")
    checked("adversarial.zero_step.a", parse_rat(zero_step["a"], "zero_step.a") == 0)
    checked("adversarial.zero_step.generator_commutator", parse_matrix(zero_step["generator_commutator"], "zero_step.generator_commutator", 2, 2) == order["hcomm"] and not is_zero(order["hcomm"]))
    checked("adversarial.zero_step.C", parse_matrix(zero_step["C_zero"], "zero_step.C", 2, 2) == eye(2))
    checked("adversarial.zero_step.commutator", is_zero(parse_matrix(zero_step["C_zero_commutator_with_U2"], "zero_step.commutator", 2, 2)))

    nuance = exact_keys(w["sign_reversal_is_adjoint_not_instability"], {"id", "classification", "U_negative_a", "U_positive_a_dagger", "residual"}, "adversarial.sign_reversal")
    uneg, _, _ = cayley_scalar_matrix(composition["h1"], Fraction(-1, 2))
    upos_star = dagger(composition["u1"])
    checked("adversarial.sign_reversal.negative", parse_matrix(nuance["U_negative_a"], "sign_reversal.negative", 2, 2) == uneg)
    checked("adversarial.sign_reversal.adjoint", parse_matrix(nuance["U_positive_a_dagger"], "sign_reversal.adjoint", 2, 2) == upos_star)
    checked("adversarial.sign_reversal.residual", is_zero(parse_matrix(nuance["residual"], "sign_reversal.residual", 2, 2)) and uneg == upos_star)


EXPECTED_METADATA = {
    "arithmetic": {
        "field": "Gaussian rationals Q(i)",
        "rational_encoding": "normalized decimal numerator and positive denominator strings",
        "matrix_orientation": "row-major JSON; column-vector action",
        "exact_algorithms": ["manual matrix multiplication", "deterministic first-nonzero-pivot Gauss-Jordan", "exact elimination determinant"],
        "forbidden_in_exact_layer": ["floating point", "LinearAlgebra.inv", "LinearAlgebra.det", "backslash solve"],
    },
    "conventions": {
        "commutator": "[X,Y]=XY-YX", "D": "I+i*a*H", "N": "I-i*a*H",
        "C": "N*D^{-1}=D^{-1}*N", "update": "D*psi_next=N*psi_current",
        "ordered_product": "P321=U3*U2*U1 acts U1 first",
    },
    "assumptions": {
        "unitarity": ["finite square complex matrix", "H^dagger=H", "a is real"],
        "order_defect": ["D_a(A) and D_b(B) invertible"],
        "commutation_iff": ["order-defect assumptions", "a*b != 0"],
    },
    "claim_classification": {
        "exactly_derived_by_julia": ["sparse star-polynomial identities", "exact matrix solves and determinants", "unitarity residuals", "noncommutative order-defect instance", "adversarial witnesses", "finite exhaustive search"],
        "numerically_tested_separately": ["random Float64 Hermitian matrices and ordered products"],
        "formally_verified_by_lean": "not supplied by this certificate; Lean proof is independent",
        "informally_interpreted": ["connection to geometric integration and finite quantum evolution"],
        "not_verified": ["infinite-dimensional operators", "convergence order", "floating-point long-time error bound", "mathematical novelty"],
    },
}


def verify_receipt(receipt_path: Path, certificate_path: Path, cert, source_root: Path):
    receipt = load_json(receipt_path, exact=False)
    keys = {"schema", "run_id", "core_sha256", "certificate_path", "certificate_sha256", "source_sha256",
            "julia_version", "timestamp_utc", "numeric_nonproof", "exact_status", "numeric_status"}
    obj = exact_keys(receipt, keys, "receipt")
    checked("receipt.schema", obj["schema"] == RECEIPT_SCHEMA)
    checked("receipt.run_id", obj["run_id"] == cert["run_id"])
    checked("receipt.core_sha256", obj["core_sha256"] == cert["core_sha256"])
    checked("receipt.certificate_sha256", obj["certificate_sha256"] == sha256_file(certificate_path))
    checked("receipt.statuses", obj["exact_status"] == "PASS" and obj["numeric_status"] == "PASS")
    checked("receipt.julia_version", obj["julia_version"] == "1.12.6")
    ensure(isinstance(obj["timestamp_utc"], str) and obj["timestamp_utc"].endswith("Z"), "receipt timestamp malformed")
    source_hashes = exact_keys(obj["source_sha256"], {"discover_operator_cayley.jl", "exact_gaussian_matrix.jl"}, "receipt.source_sha256")
    for name, expected in source_hashes.items():
        checked("receipt.source." + name, expected == sha256_file(source_root / name) == cert["core"]["source_sha256"][name])
    numeric = exact_keys(obj["numeric_nonproof"], {"classification", "seed", "trials_per_dimension", "matrix_dimensions",
                                                               "factors_per_product", "single_factor_checks", "ordered_product_checks",
                                                               "residual_norm", "acceptance_limit", "acceptance_limit_provenance",
                                                               "max_single_factor_unitarity_residual", "max_three_factor_unitarity_residual"},
                         "receipt.numeric_nonproof")
    checked("numeric.classification", numeric["classification"] == "NUMERICALLY_TESTED_NON_PROOF")
    checked("numeric.fixed_configuration", numeric["seed"] == 20260905 and numeric["trials_per_dimension"] == 512 and
            numeric["matrix_dimensions"] == [2, 3, 4] and numeric["factors_per_product"] == 3)
    checked("numeric.counts", numeric["single_factor_checks"] == 4608 and numeric["ordered_product_checks"] == 1536)
    checked("numeric.norm", numeric["residual_norm"] == "Euclidean induced operator 2-norm via LinearAlgebra.opnorm(A, 2)")
    checked("numeric.limit_provenance", numeric["acceptance_limit_provenance"] ==
            "independently fixed in source before execution; not certificate-controlled")
    try:
        stated_limit = Decimal(numeric["acceptance_limit"])
        single = Decimal(numeric["max_single_factor_unitarity_residual"])
        product = Decimal(numeric["max_three_factor_unitarity_residual"])
    except (InvalidOperation, TypeError) as exc:
        raise ValidationError(f"numeric receipt contains invalid decimal: {exc}") from exc
    checked("numeric.independent_limit", stated_limit == FIXED_NUMERIC_LIMIT)
    checked("numeric.single_finite", single.is_finite() and single >= 0)
    checked("numeric.product_finite", product.is_finite() and product >= 0)
    checked("numeric.single_accepted", single <= FIXED_NUMERIC_LIMIT)
    checked("numeric.product_accepted", product <= FIXED_NUMERIC_LIMIT)


def validate(certificate_path: Path, receipt_path: Path | None, source_root: Path | None):
    cert = load_json(certificate_path, exact=True)
    exact_keys(cert, {"schema", "core", "core_sha256", "run_id"}, "certificate")
    checked("certificate.schema", cert["schema"] == CERT_SCHEMA)
    ensure(isinstance(cert["core_sha256"], str) and HEX64_RE.fullmatch(cert["core_sha256"]), "core_sha256 malformed")
    core_hash = sha256_bytes(canonical_bytes(cert["core"]))
    checked("certificate.core_sha256", cert["core_sha256"] == core_hash)
    checked("certificate.run_id", cert["run_id"] == "exp002-" + core_hash[:24])
    core_keys = {"schema", "arithmetic", "conventions", "assumptions", "source_sha256", "julia_version",
                 "symbolic_star_polynomial_derivation", "exact_instances", "composition", "order_defect",
                 "exact_vector_norm_checks", "edge_cases", "adversarial_witnesses", "exhaustive_counterexample_search",
                 "claim_classification"}
    core = exact_keys(cert["core"], core_keys, "core")
    checked("core.schema", core["schema"] == CORE_SCHEMA)
    checked("core.julia_version", core["julia_version"] == "1.12.6")
    for key, expected in EXPECTED_METADATA.items():
        checked("core.metadata." + key, core[key] == expected)
    source_hashes = exact_keys(core["source_sha256"], {"discover_operator_cayley.jl", "exact_gaussian_matrix.jl"}, "core.source_sha256")
    checked("core.source_hash_format", all(isinstance(v, str) and HEX64_RE.fullmatch(v) for v in source_hashes.values()))
    if source_root is not None:
        for name, expected in source_hashes.items():
            checked("core.source." + name, sha256_file(source_root / name) == expected)
    verify_symbolic(core["symbolic_star_polynomial_derivation"])
    ensure(isinstance(core["exact_instances"], list) and len(core["exact_instances"]) == 3,
           "exact_instances: expected exactly three")
    instances = []
    for index, record in enumerate(core["exact_instances"]):
        parsed = verify_cayley_record(record, f"exact_instances[{index}]", has_id=True, require_hermitian=True)
        parsed["id"] = record["id"]
        instances.append(parsed)
    composition = verify_composition(core, instances)
    verify_vectors(core["exact_vector_norm_checks"], composition)
    order = verify_order_defect(core["order_defect"], composition)
    ensure(isinstance(core["edge_cases"], list) and len(core["edge_cases"]) == 6, "edge_cases: expected exactly six")
    edge_ids = []
    for index, record in enumerate(core["edge_cases"]):
        verify_cayley_record(record, f"edge_cases[{index}]", has_id=True, require_hermitian=True)
        edge_ids.append(record["id"])
    checked("edge_cases.ids", edge_ids == ["scalar", "zero_step", "zero_generator", "negative_step", "rank_deficient", "repeated_spectrum"])
    verify_adversarial(core["adversarial_witnesses"], composition, order)
    verify_search(core["exhaustive_counterexample_search"])
    if receipt_path is not None:
        ensure(source_root is not None, "--receipt requires --source-root")
        verify_receipt(receipt_path, certificate_path, cert, source_root)
    return cert


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--source-root", type=Path)
    args = parser.parse_args()
    try:
        validate(args.certificate, args.receipt, args.source_root)
    except ValidationError as exc:
        print(f"VALIDATION_STATUS=FAIL\nREASON={exc}", file=sys.stderr)
        return 1
    print("VALIDATION_STATUS=PASS")
    print(f"CHECKS={len(CHECKS)}")
    print(f"CERTIFICATE_SHA256={sha256_file(args.certificate)}")
    print("BOUNDARY=finite certificate claims reconstructed; universal theorem verification remains Lean-only")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
