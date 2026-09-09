#!/usr/bin/env python3
"""Strict independent validator for the Exp003 Step-3 exact certificate.

The validator reconstructs every Gaussian-rational matrix and every formal
noncommutative word-polynomial field.  It does not establish the universal
Lean identity or operator-norm theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


CERT_SCHEMA = "ndea.exp003.step3.split_unsplit_certificate.v1"
CORE_SCHEMA = "ndea.exp003.step3.split_unsplit_core.v1"
RECEIPT_SCHEMA = "ndea.exp003.step3.split_unsplit_run_receipt.v1"
INT_RE = re.compile(r"(?:0|-[1-9][0-9]*|[1-9][0-9]*)\Z")
POS_RE = re.compile(r"[1-9][0-9]*\Z")
HEX64_RE = re.compile(r"[0-9a-f]{64}\Z")
ALLOWED_WORD_SYMBOLS = {"X", "Y", "R_A", "R_B", "R_sum"}


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
    ensure(
        actual == keys,
        f"{where}: key set mismatch; missing={sorted(keys-actual)} "
        f"extra={sorted(actual-keys)}",
    )
    return value


def no_duplicate_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValidationError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def reject_float(token: str):
    raise ValidationError(f"floating JSON number forbidden: {token}")


def load_json(path: Path):
    try:
        with path.open("r", encoding="utf-8") as stream:
            return json.load(
                stream,
                object_pairs_hook=no_duplicate_object,
                parse_float=reject_float,
                parse_constant=lambda token: (_ for _ in ()).throw(
                    ValidationError(f"non-finite JSON constant forbidden: {token}")
                ),
            )
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValidationError(f"cannot parse {path}: {exc}") from exc


def canonical_bytes(value) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
    except OSError as exc:
        raise ValidationError(f"cannot hash {path}: {exc}") from exc
    return digest.hexdigest()


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
        return G(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def __truediv__(self, other: "G") -> "G":
        ensure(other != ZERO, "division by zero in exact reconstruction")
        denominator = other.re * other.re + other.im * other.im
        return G(
            (self.re * other.re + self.im * other.im) / denominator,
            (self.im * other.re - self.re * other.im) / denominator,
        )

    def conj(self) -> "G":
        return G(self.re, -self.im)


ZERO = G()
ONE = G(Fraction(1))
I = G(Fraction(0), Fraction(1))


def parse_rat(value, where: str) -> Fraction:
    obj = exact_keys(value, {"num", "den"}, where)
    numerator, denominator = obj["num"], obj["den"]
    ensure(
        isinstance(numerator, str) and INT_RE.fullmatch(numerator),
        f"{where}.num: noncanonical integer string",
    )
    ensure(
        isinstance(denominator, str) and POS_RE.fullmatch(denominator),
        f"{where}.den: noncanonical positive denominator",
    )
    result = Fraction(int(numerator), int(denominator))
    ensure(
        str(result.numerator) == numerator
        and str(result.denominator) == denominator,
        f"{where}: rational must be normalized",
    )
    return result


def rat_json(value: Fraction):
    return {"num": str(value.numerator), "den": str(value.denominator)}


def parse_g(value, where: str) -> G:
    obj = exact_keys(value, {"re", "im"}, where)
    return G(
        parse_rat(obj["re"], where + ".re"),
        parse_rat(obj["im"], where + ".im"),
    )


def g_json(value: G):
    return {"re": rat_json(value.re), "im": rat_json(value.im)}


Matrix = tuple[tuple[G, ...], ...]
Word = tuple[str, ...]
NCPoly = dict[Word, Fraction]


def parse_matrix(
    value, where: str, rows: int | None = None, columns: int | None = None
) -> Matrix:
    ensure(isinstance(value, list) and value, f"{where}: expected nonempty matrix")
    ensure(
        all(isinstance(row, list) and row for row in value),
        f"{where}: expected nonempty rows",
    )
    width = len(value[0])
    ensure(all(len(row) == width for row in value), f"{where}: ragged matrix")
    if rows is not None:
        ensure(len(value) == rows, f"{where}: wrong row count")
    if columns is not None:
        ensure(width == columns, f"{where}: wrong column count")
    return tuple(
        tuple(
            parse_g(cell, f"{where}[{row_index}][{column_index}]")
            for column_index, cell in enumerate(row)
        )
        for row_index, row in enumerate(value)
    )


def shape(matrix: Matrix) -> tuple[int, int]:
    return len(matrix), len(matrix[0])


def zero_matrix(rows: int, columns: int) -> Matrix:
    return tuple(tuple(ZERO for _ in range(columns)) for _ in range(rows))


def eye(n: int) -> Matrix:
    return tuple(
        tuple(ONE if row == column else ZERO for column in range(n))
        for row in range(n)
    )


def madd(left: Matrix, right: Matrix) -> Matrix:
    ensure(shape(left) == shape(right), "matrix add dimension mismatch")
    return tuple(
        tuple(x + y for x, y in zip(left_row, right_row))
        for left_row, right_row in zip(left, right)
    )


def mneg(matrix: Matrix) -> Matrix:
    return tuple(tuple(-cell for cell in row) for row in matrix)


def msub(left: Matrix, right: Matrix) -> Matrix:
    return madd(left, mneg(right))


def mscale(coefficient: G, matrix: Matrix) -> Matrix:
    return tuple(
        tuple(coefficient * cell for cell in row) for row in matrix
    )


def mmul(left: Matrix, right: Matrix) -> Matrix:
    left_rows, shared = shape(left)
    right_rows, right_columns = shape(right)
    ensure(shared == right_rows, "matrix multiply dimension mismatch")
    return tuple(
        tuple(
            sum(
                (left[row][index] * right[index][column] for index in range(shared)),
                ZERO,
            )
            for column in range(right_columns)
        )
        for row in range(left_rows)
    )


def mul_chain(first: Matrix, *rest: Matrix) -> Matrix:
    result = first
    for factor in rest:
        result = mmul(result, factor)
    return result


def dagger(matrix: Matrix) -> Matrix:
    rows, columns = shape(matrix)
    return tuple(
        tuple(matrix[row][column].conj() for row in range(rows))
        for column in range(columns)
    )


def is_zero(matrix: Matrix) -> bool:
    return all(cell == ZERO for row in matrix for cell in row)


def is_hermitian(matrix: Matrix) -> bool:
    rows, columns = shape(matrix)
    return rows == columns and matrix == dagger(matrix)


def inverse_with_trace(matrix: Matrix):
    n, columns = shape(matrix)
    ensure(n == columns, "inverse requires square matrix")
    augmented = [list(matrix[row]) + list(eye(n)[row]) for row in range(n)]
    trace = []
    for column in range(n):
        pivot_row = next(
            (row for row in range(column, n) if augmented[row][column] != ZERO),
            None,
        )
        if pivot_row is None:
            trace.append({"operation": "singular", "column": column + 1})
            return None, trace
        if pivot_row != column:
            augmented[column], augmented[pivot_row] = (
                augmented[pivot_row],
                augmented[column],
            )
            trace.append(
                {"operation": "swap", "row_a": column + 1, "row_b": pivot_row + 1}
            )
        pivot = augmented[column][column]
        trace.append(
            {"operation": "scale", "row": column + 1, "divisor": g_json(pivot)}
        )
        augmented[column] = [cell / pivot for cell in augmented[column]]
        for row in range(n):
            if row == column:
                continue
            factor = augmented[row][column]
            if factor != ZERO:
                trace.append(
                    {
                        "operation": "eliminate",
                        "source_row": column + 1,
                        "target_row": row + 1,
                        "factor": g_json(factor),
                    }
                )
                augmented[row] = [
                    cell - factor * source
                    for cell, source in zip(augmented[row], augmented[column])
                ]
    return tuple(tuple(row[n:]) for row in augmented), trace


def nc_clean(poly: NCPoly) -> NCPoly:
    return {word: coefficient for word, coefficient in poly.items() if coefficient}


def nc_constant(coefficient: Fraction) -> NCPoly:
    return {} if not coefficient else {(): coefficient}


def nc_variable(name: str) -> NCPoly:
    return {(name,): Fraction(1)}


def nc_add(left: NCPoly, right: NCPoly) -> NCPoly:
    result = dict(left)
    for word, coefficient in right.items():
        result[word] = result.get(word, Fraction(0)) + coefficient
    return nc_clean(result)


def nc_neg(poly: NCPoly) -> NCPoly:
    return {word: -coefficient for word, coefficient in poly.items()}


def nc_sub(left: NCPoly, right: NCPoly) -> NCPoly:
    return nc_add(left, nc_neg(right))


def nc_scale(coefficient: Fraction, poly: NCPoly) -> NCPoly:
    return nc_clean(
        {word: coefficient * value for word, value in poly.items()}
    )


def nc_mul(left: NCPoly, right: NCPoly) -> NCPoly:
    result: NCPoly = {}
    for left_word, left_coefficient in left.items():
        for right_word, right_coefficient in right.items():
            word = left_word + right_word
            result[word] = result.get(word, Fraction(0)) + (
                left_coefficient * right_coefficient
            )
    return nc_clean(result)


def nc_product(first: NCPoly, *rest: NCPoly) -> NCPoly:
    result = first
    for factor in rest:
        result = nc_mul(result, factor)
    return result


def parse_nc(value, where: str) -> NCPoly:
    ensure(isinstance(value, list), f"{where}: polynomial must be an array")
    result: NCPoly = {}
    previous_key = None
    for index, term in enumerate(value):
        obj = exact_keys(term, {"coefficient", "word"}, f"{where}[{index}]")
        word_value = obj["word"]
        ensure(
            isinstance(word_value, list)
            and all(
                isinstance(symbol, str) and symbol in ALLOWED_WORD_SYMBOLS
                for symbol in word_value
            ),
            f"{where}[{index}].word: invalid symbol sequence",
        )
        word = tuple(word_value)
        sort_key = (len(word), "\0".join(word))
        ensure(
            previous_key is None or previous_key < sort_key,
            f"{where}: terms are not strictly canonically ordered",
        )
        ensure(word not in result, f"{where}: duplicate word")
        coefficient = parse_rat(obj["coefficient"], f"{where}[{index}].coefficient")
        ensure(coefficient != 0, f"{where}: zero coefficient forbidden")
        result[word] = coefficient
        previous_key = sort_key
    return result


def verify_formal(value) -> None:
    keys = {
        "symbols",
        "right_inverse_relations",
        "left_inverse_relations",
        "cayley_affine_reductions",
        "original_defect",
        "affine_defect_expression",
        "affine_defect_expanded",
        "first_rhs_term_reduction",
        "denominator_product_gap",
        "resolvent_bridge",
        "scaled_target_original",
        "scaled_target_reduced",
        "final_residual",
        "rewrite_trace",
    }
    obj = exact_keys(value, keys, "core.formal_noncommutative_derivation")
    expected_symbols = {
        "X": "i*alpha*A",
        "Y": "i*alpha*B",
        "R_A": "(1+X)^-1",
        "R_B": "(1+Y)^-1",
        "R_sum": "(1+X+Y)^-1",
        "multiplication": "noncommutative; coefficients are central rationals",
    }
    checked("formal.symbols", obj["symbols"] == expected_symbols)

    one = nc_constant(Fraction(1))
    X, Y = nc_variable("X"), nc_variable("Y")
    RA, RB, RS = (
        nc_variable("R_A"),
        nc_variable("R_B"),
        nc_variable("R_sum"),
    )
    DA, DB = nc_add(one, X), nc_add(one, Y)
    DS = nc_add(nc_add(one, X), Y)
    NA, NB = nc_sub(one, X), nc_sub(one, Y)
    NS = nc_sub(nc_sub(one, X), Y)

    relation_sets = [
        (
            "right_inverse_relations",
            [
                ("D_A_R_A", nc_mul(DA, RA), one),
                ("D_B_R_B", nc_mul(DB, RB), one),
                ("D_sum_R_sum", nc_mul(DS, RS), one),
            ],
        ),
        (
            "left_inverse_relations",
            [
                ("R_A_D_A", nc_mul(RA, DA), one),
                ("R_B_D_B", nc_mul(RB, DB), one),
                ("R_sum_D_sum", nc_mul(RS, DS), one),
            ],
        ),
    ]
    for field, expected in relation_sets:
        records = obj[field]
        ensure(
            isinstance(records, list) and len(records) == len(expected),
            f"formal.{field}: wrong length",
        )
        for index, (expected_id, expected_lhs, expected_rhs) in enumerate(expected):
            record = exact_keys(
                records[index], {"id", "lhs", "rhs"}, f"formal.{field}[{index}]"
            )
            checked(f"formal.{field}[{index}].id", record["id"] == expected_id)
            checked(
                f"formal.{field}[{index}].lhs",
                parse_nc(record["lhs"], f"formal.{field}[{index}].lhs")
                == expected_lhs,
            )
            checked(
                f"formal.{field}[{index}].rhs",
                parse_nc(record["rhs"], f"formal.{field}[{index}].rhs")
                == expected_rhs,
            )

    original_A, original_B, original_sum = (
        nc_mul(NA, RA),
        nc_mul(NB, RB),
        nc_mul(NS, RS),
    )
    affine_A, affine_B, affine_sum = (
        nc_sub(nc_scale(Fraction(2), RA), one),
        nc_sub(nc_scale(Fraction(2), RB), one),
        nc_sub(nc_scale(Fraction(2), RS), one),
    )
    expected_affine = [
        ("A", original_A, affine_A, ["D_A_R_A"]),
        ("B", original_B, affine_B, ["D_B_R_B"]),
        ("sum", original_sum, affine_sum, ["D_sum_R_sum"]),
    ]
    reductions = obj["cayley_affine_reductions"]
    ensure(
        isinstance(reductions, list) and len(reductions) == 3,
        "formal.cayley_affine_reductions: wrong length",
    )
    for index, (expected_id, original, reduced, uses) in enumerate(expected_affine):
        record = exact_keys(
            reductions[index],
            {"id", "original", "reduced", "uses"},
            f"formal.cayley_affine_reductions[{index}]",
        )
        checked(f"formal.affine[{index}].id", record["id"] == expected_id)
        checked(
            f"formal.affine[{index}].original",
            parse_nc(record["original"], f"formal.affine[{index}].original")
            == original,
        )
        checked(
            f"formal.affine[{index}].reduced",
            parse_nc(record["reduced"], f"formal.affine[{index}].reduced")
            == reduced,
        )
        checked(f"formal.affine[{index}].uses", record["uses"] == uses)

    original_defect = nc_sub(nc_mul(original_A, original_B), original_sum)
    affine_defect = nc_sub(nc_mul(affine_A, affine_B), affine_sum)
    checked(
        "formal.original_defect",
        parse_nc(obj["original_defect"], "formal.original_defect")
        == original_defect,
    )
    checked(
        "formal.affine_defect_expression",
        parse_nc(obj["affine_defect_expression"], "formal.affine_defect_expression")
        == affine_defect,
    )
    checked(
        "formal.affine_defect_expanded",
        parse_nc(obj["affine_defect_expanded"], "formal.affine_defect_expanded")
        == affine_defect,
    )

    first_original = nc_product(X, RA, Y, RB)
    first_after_X = nc_product(nc_sub(one, RA), Y, RB)
    first_reduced = nc_mul(nc_sub(one, RA), nc_sub(one, RB))
    first = exact_keys(
        obj["first_rhs_term_reduction"],
        {"original", "after_X_R_A", "reduced", "uses"},
        "formal.first_rhs_term_reduction",
    )
    checked(
        "formal.first.original",
        parse_nc(first["original"], "formal.first.original") == first_original,
    )
    checked(
        "formal.first.after_X_R_A",
        parse_nc(first["after_X_R_A"], "formal.first.after_X_R_A")
        == first_after_X,
    )
    checked(
        "formal.first.reduced",
        parse_nc(first["reduced"], "formal.first.reduced") == first_reduced,
    )
    checked(
        "formal.first.uses", first["uses"] == ["D_A_R_A", "D_B_R_B"]
    )

    product_gap = nc_sub(nc_mul(DB, DA), DS)
    gap_expanded = nc_mul(Y, X)
    gap = exact_keys(
        obj["denominator_product_gap"],
        {"expression", "expanded", "residual"},
        "formal.denominator_product_gap",
    )
    checked(
        "formal.gap.expression",
        parse_nc(gap["expression"], "formal.gap.expression") == product_gap,
    )
    checked(
        "formal.gap.expanded",
        parse_nc(gap["expanded"], "formal.gap.expanded") == gap_expanded,
    )
    checked(
        "formal.gap.residual",
        parse_nc(gap["residual"], "formal.gap.residual")
        == nc_sub(product_gap, gap_expanded)
        == {},
    )

    bridge_context = nc_product(RS, product_gap, RA, RB)
    bridge_expanded = nc_product(RS, Y, X, RA, RB)
    product_context = nc_product(RS, DB, DA, RA, RB)
    sum_context = nc_product(RS, DS, RA, RB)
    bridge_reduced = nc_sub(RS, nc_mul(RA, RB))
    bridge = exact_keys(
        obj["resolvent_bridge"],
        {
            "gap_context",
            "expanded",
            "product_context",
            "product_context_reduced",
            "sum_context",
            "sum_context_reduced",
            "reduced",
            "uses",
        },
        "formal.resolvent_bridge",
    )
    bridge_fields = {
        "gap_context": bridge_context,
        "expanded": bridge_expanded,
        "product_context": product_context,
        "product_context_reduced": RS,
        "sum_context": sum_context,
        "sum_context_reduced": nc_mul(RA, RB),
        "reduced": bridge_reduced,
    }
    for field, expected in bridge_fields.items():
        checked(
            "formal.bridge." + field,
            parse_nc(bridge[field], "formal.bridge." + field) == expected,
        )
    checked(
        "formal.bridge.uses",
        bridge["uses"] == ["D_A_R_A", "D_B_R_B", "R_sum_D_sum"],
    )

    target_original = nc_scale(
        Fraction(2), nc_sub(first_original, bridge_expanded)
    )
    target_reduced = nc_scale(
        Fraction(2), nc_sub(first_reduced, bridge_reduced)
    )
    checked(
        "formal.target.original",
        parse_nc(obj["scaled_target_original"], "formal.target.original")
        == target_original,
    )
    checked(
        "formal.target.reduced",
        parse_nc(obj["scaled_target_reduced"], "formal.target.reduced")
        == target_reduced,
    )
    checked(
        "formal.final_residual",
        parse_nc(obj["final_residual"], "formal.final_residual")
        == nc_sub(affine_defect, target_reduced)
        == {},
    )
    expected_trace = [
        "replace each Cayley factor (1-X)R by 2R-1 using its right inverse law",
        "expand the split-minus-unsplit defect without commuting any symbols",
        "reduce X*R_A and Y*R_B to 1-R_A and 1-R_B",
        "expand (1+Y)(1+X)-(1+X+Y) to Y*X",
        "sandwich that gap by R_sum on the left and R_A*R_B on the right",
        "cancel only adjacent certified inverse pairs to obtain R_sum-R_A*R_B",
        "the reduced target equals the expanded defect exactly",
        "substitute X=i*alpha*A and Y=i*alpha*B, so i^2=-1 yields the stated 2*alpha^2 formula",
    ]
    checked("formal.rewrite_trace", obj["rewrite_trace"] == expected_trace)


CASE_KEYS = {
    "id",
    "classification",
    "dimension",
    "alpha",
    "A",
    "B",
    "A_plus_B",
    "D_A",
    "D_B",
    "D_sum",
    "N_A",
    "N_B",
    "N_sum",
    "R_A",
    "R_B",
    "R_sum",
    "C_A",
    "C_B",
    "C_sum",
    "split_product",
    "local_defect",
    "rhs_first_term",
    "rhs_second_term",
    "factorized_rhs",
    "coefficient",
    "generator_commutator",
    "generators_commute",
    "local_defect_zero",
    "pivot_traces",
    "residuals",
}
RESIDUAL_KEYS = {
    "A_hermitian",
    "B_hermitian",
    "sum_hermitian",
    "sum_definition",
    "D_A_R_A_minus_I",
    "R_A_D_A_minus_I",
    "D_B_R_B_minus_I",
    "R_B_D_B_minus_I",
    "D_sum_R_sum_minus_I",
    "R_sum_D_sum_minus_I",
    "C_A_minus_N_A_R_A",
    "C_B_minus_N_B_R_B",
    "C_sum_minus_N_sum_R_sum",
    "split_minus_C_A_C_B",
    "local_defect_definition",
    "factorized_rhs_definition",
    "exact_identity",
}


def cayley_data(generator: Matrix, alpha: Fraction):
    n, columns = shape(generator)
    ensure(n == columns, "Cayley generator must be square")
    identity = eye(n)
    skew = mscale(I * G(alpha), generator)
    denominator = madd(identity, skew)
    numerator = msub(identity, skew)
    resolvent, trace = inverse_with_trace(denominator)
    ensure(resolvent is not None, "unexpected singular Hermitian denominator")
    factor = mmul(numerator, resolvent)
    return {
        "D": denominator,
        "N": numerator,
        "R": resolvent,
        "C": factor,
        "trace": trace,
    }


def verify_case(record, where: str, expected_id: str, expected_classification: str):
    obj = exact_keys(record, CASE_KEYS, where)
    checked(where + ".id", obj["id"] == expected_id)
    checked(where + ".classification", obj["classification"] == expected_classification)
    n = obj["dimension"]
    ensure(type(n) is int and 1 <= n <= 32, f"{where}.dimension: invalid")
    alpha = parse_rat(obj["alpha"], where + ".alpha")
    A = parse_matrix(obj["A"], where + ".A", n, n)
    B = parse_matrix(obj["B"], where + ".B", n, n)
    checked(where + ".A.Hermitian", is_hermitian(A))
    checked(where + ".B.Hermitian", is_hermitian(B))
    sum_generator = madd(A, B)
    checked(
        where + ".A_plus_B",
        parse_matrix(obj["A_plus_B"], where + ".A_plus_B", n, n)
        == sum_generator,
    )
    data_A, data_B, data_sum = (
        cayley_data(A, alpha),
        cayley_data(B, alpha),
        cayley_data(sum_generator, alpha),
    )
    for label, data in (("A", data_A), ("B", data_B), ("sum", data_sum)):
        for prefix, key in (("D", "D"), ("N", "N"), ("R", "R"), ("C", "C")):
            field = f"{prefix}_{label}"
            checked(
                where + "." + field,
                parse_matrix(obj[field], where + "." + field, n, n) == data[key],
            )
    traces = exact_keys(obj["pivot_traces"], {"A", "B", "sum"}, where + ".pivot_traces")
    for label, data in (("A", data_A), ("B", data_B), ("sum", data_sum)):
        checked(where + ".pivot_trace." + label, traces[label] == data["trace"])

    split_product = mmul(data_A["C"], data_B["C"])
    defect = msub(split_product, data_sum["C"])
    first_term = mul_chain(data_sum["R"], B, A, data_A["R"], data_B["R"])
    second_term = mul_chain(A, data_A["R"], B, data_B["R"])
    coefficient = Fraction(2) * alpha * alpha
    rhs = mscale(G(coefficient), msub(first_term, second_term))
    commutator = msub(mmul(A, B), mmul(B, A))
    matrix_fields = {
        "split_product": split_product,
        "local_defect": defect,
        "rhs_first_term": first_term,
        "rhs_second_term": second_term,
        "factorized_rhs": rhs,
        "generator_commutator": commutator,
    }
    for field, expected in matrix_fields.items():
        checked(
            where + "." + field,
            parse_matrix(obj[field], where + "." + field, n, n) == expected,
        )
    checked(
        where + ".coefficient",
        parse_rat(obj["coefficient"], where + ".coefficient") == coefficient,
    )
    checked(
        where + ".generators_commute",
        obj["generators_commute"] is is_zero(commutator),
    )
    checked(
        where + ".local_defect_zero",
        obj["local_defect_zero"] is is_zero(defect),
    )

    identity = eye(n)
    residuals = {
        "A_hermitian": msub(dagger(A), A),
        "B_hermitian": msub(dagger(B), B),
        "sum_hermitian": msub(dagger(sum_generator), sum_generator),
        "sum_definition": msub(sum_generator, madd(A, B)),
        "D_A_R_A_minus_I": msub(mmul(data_A["D"], data_A["R"]), identity),
        "R_A_D_A_minus_I": msub(mmul(data_A["R"], data_A["D"]), identity),
        "D_B_R_B_minus_I": msub(mmul(data_B["D"], data_B["R"]), identity),
        "R_B_D_B_minus_I": msub(mmul(data_B["R"], data_B["D"]), identity),
        "D_sum_R_sum_minus_I": msub(
            mmul(data_sum["D"], data_sum["R"]), identity
        ),
        "R_sum_D_sum_minus_I": msub(
            mmul(data_sum["R"], data_sum["D"]), identity
        ),
        "C_A_minus_N_A_R_A": msub(data_A["C"], mmul(data_A["N"], data_A["R"])),
        "C_B_minus_N_B_R_B": msub(data_B["C"], mmul(data_B["N"], data_B["R"])),
        "C_sum_minus_N_sum_R_sum": msub(
            data_sum["C"], mmul(data_sum["N"], data_sum["R"])
        ),
        "split_minus_C_A_C_B": msub(split_product, mmul(data_A["C"], data_B["C"])),
        "local_defect_definition": msub(
            defect, msub(split_product, data_sum["C"])
        ),
        "factorized_rhs_definition": msub(
            rhs, mscale(G(coefficient), msub(first_term, second_term))
        ),
        "exact_identity": msub(defect, rhs),
    }
    residual_obj = exact_keys(obj["residuals"], RESIDUAL_KEYS, where + ".residuals")
    for field, expected in residuals.items():
        supplied = parse_matrix(
            residual_obj[field], where + ".residuals." + field, n, n
        )
        checked(where + ".residuals." + field, supplied == expected)
        checked(where + ".zero." + field, is_zero(expected))
    return {
        "alpha": alpha,
        "A": A,
        "B": B,
        "sum": sum_generator,
        "commutator": commutator,
        "defect": defect,
    }


EXPECTED_ARITHMETIC = {
    "field": "Gaussian rationals Q(i)",
    "rational_encoding": "normalized decimal numerator and positive denominator strings",
    "matrix_orientation": "row-major JSON; column-vector action",
    "exact_algorithms": [
        "manual matrix multiplication",
        "deterministic first-nonzero-pivot Gauss-Jordan",
        "free noncommutative word-polynomial expansion",
    ],
    "forbidden_in_exact_layer": [
        "floating point",
        "LinearAlgebra.inv",
        "backslash solve",
        "numerical matrix norm",
    ],
}
EXPECTED_CONVENTIONS = {
    "D": "I+i*alpha*H",
    "N": "I-i*alpha*H",
    "R": "D^-1",
    "C": "N*R",
    "split_order": "C_alpha(A)*C_alpha(B); B acts first on column vectors",
    "local_defect": "C_alpha(A)*C_alpha(B)-C_alpha(A+B)",
    "exact_rhs": "2*alpha^2*(R_sum*B*A*R_A*R_B-A*R_A*B*R_B)",
}
EXPECTED_ASSUMPTIONS = [
    "finite square complex matrices",
    "A and B Hermitian",
    "alpha real, including zero and negative values",
]
EXPECTED_CLASSIFICATION = {
    "exactly_derived_by_julia": [
        "five Gaussian-rational matrix instances",
        "all Cayley inverses and identity residuals",
        "the split-versus-unsplit factorization residuals",
        "a free noncommutative algebra expansion",
        "commutative-collapse and corrected large-step linear-bound witnesses",
    ],
    "formally_verified_by_lean": "not supplied by this certificate; universal identity and operator-norm bound remain Lean-only",
    "not_claimed": [
        "floating-point evidence",
        "infinite-dimensional operators",
        "telescoping",
        "continuous-exponential comparison",
    ],
}


def verify_negative_controls(value, cases: dict[str, dict]) -> None:
    obj = exact_keys(
        value,
        {"commutative_collapse", "linear_scaling_large_step"},
        "core.negative_controls",
    )
    commutative = exact_keys(
        obj["commutative_collapse"],
        {"case_id", "generators_commute", "local_defect_nonzero"},
        "negative_controls.commutative_collapse",
    )
    checked(
        "controls.commutative.case_id",
        commutative["case_id"] == "commutative_scalar_one",
    )
    commutative_case = cases[commutative["case_id"]]
    checked(
        "controls.commutative.commute",
        commutative["generators_commute"] is True
        and is_zero(commutative_case["commutator"]),
    )
    checked(
        "controls.commutative.defect_nonzero",
        commutative["local_defect_nonzero"] is True
        and not is_zero(commutative_case["defect"]),
    )

    linear = exact_keys(
        obj["linear_scaling_large_step"],
        {
            "case_id",
            "statement_refuted",
            "norm_semantics",
            "alpha",
            "A_operator_norm",
            "B_operator_norm",
            "local_defect_modulus_squared",
            "claimed_rhs",
            "claimed_rhs_squared",
            "strict_violation",
            "scope_note",
        },
        "negative_controls.linear_scaling_large_step",
    )
    checked(
        "controls.linear.case_id", linear["case_id"] == "linear_scaling_large_step"
    )
    checked(
        "controls.linear.statement",
        linear["statement_refuted"]
        == "norm(E_local(alpha)) <= 4*abs(alpha)*norm(Ahat)*norm(Bhat)",
    )
    checked(
        "controls.linear.norm_semantics",
        linear["norm_semantics"]
        == "Euclidean induced operator norm; for a 1x1 scalar matrix this is complex modulus",
    )
    checked(
        "controls.linear.scope_note",
        linear["scope_note"]
        == "A small-step witness is impossible because alpha^2 <= abs(alpha) for abs(alpha) <= 1",
    )
    case = cases[linear["case_id"]]
    ensure(shape(case["A"]) == (1, 1), "linear witness must be scalar")
    alpha = case["alpha"]
    norm_A, norm_B = abs(case["A"][0][0].re), abs(case["B"][0][0].re)
    ensure(case["A"][0][0].im == 0 and case["B"][0][0].im == 0,
           "linear witness generators must be real scalars")
    defect_scalar = case["defect"][0][0]
    defect_modulus_squared = defect_scalar.re**2 + defect_scalar.im**2
    claimed_rhs = Fraction(4) * abs(alpha) * norm_A * norm_B
    claimed_rhs_squared = claimed_rhs**2
    checked("controls.linear.alpha", parse_rat(linear["alpha"], "controls.linear.alpha") == alpha == 10)
    checked("controls.linear.norm_A", parse_rat(linear["A_operator_norm"], "controls.linear.norm_A") == norm_A == Fraction(1, 10))
    checked("controls.linear.norm_B", parse_rat(linear["B_operator_norm"], "controls.linear.norm_B") == norm_B == Fraction(1, 10))
    checked("controls.linear.defect_squared", parse_rat(linear["local_defect_modulus_squared"], "controls.linear.defect_squared") == defect_modulus_squared == Fraction(4, 5))
    checked("controls.linear.rhs", parse_rat(linear["claimed_rhs"], "controls.linear.rhs") == claimed_rhs == Fraction(2, 5))
    checked("controls.linear.rhs_squared", parse_rat(linear["claimed_rhs_squared"], "controls.linear.rhs_squared") == claimed_rhs_squared == Fraction(4, 25))
    checked(
        "controls.linear.strict_violation",
        linear["strict_violation"] is True
        and defect_modulus_squared > claimed_rhs_squared,
    )


def verify_receipt(
    receipt_path: Path, certificate_path: Path, certificate, source_root: Path
) -> None:
    receipt = exact_keys(
        load_json(receipt_path),
        {
            "schema",
            "run_id",
            "core_sha256",
            "certificate_path",
            "certificate_sha256",
            "source_sha256",
            "julia_version",
            "timestamp_utc",
            "exact_case_count",
            "exact_status",
            "numeric_layer",
        },
        "receipt",
    )
    checked("receipt.schema", receipt["schema"] == RECEIPT_SCHEMA)
    checked("receipt.run_id", receipt["run_id"] == certificate["run_id"])
    checked(
        "receipt.core_sha256",
        receipt["core_sha256"] == certificate["core_sha256"],
    )
    checked(
        "receipt.certificate_path",
        receipt["certificate_path"] == "certificates/split_unsplit_core.json",
    )
    checked(
        "receipt.certificate_sha256",
        receipt["certificate_sha256"] == sha256_file(certificate_path),
    )
    checked("receipt.julia_version", receipt["julia_version"] == "1.12.6")
    checked(
        "receipt.timestamp",
        isinstance(receipt["timestamp_utc"], str)
        and receipt["timestamp_utc"].endswith("Z"),
    )
    checked(
        "receipt.status",
        receipt["exact_case_count"] == 5
        and receipt["exact_status"] == "PASS"
        and receipt["numeric_layer"] == "ABSENT_BY_DESIGN",
    )
    source_hashes = exact_keys(
        receipt["source_sha256"],
        {"discover_split_unsplit.jl", "exact_gaussian_matrix.jl"},
        "receipt.source_sha256",
    )
    for name, digest in source_hashes.items():
        checked(
            "receipt.source." + name,
            digest
            == certificate["core"]["source_sha256"][name]
            == sha256_file(source_root / name),
        )


def validate(
    certificate_path: Path,
    receipt_path: Path | None,
    source_root: Path | None,
):
    certificate = exact_keys(
        load_json(certificate_path),
        {"schema", "core", "core_sha256", "run_id"},
        "certificate",
    )
    checked("certificate.schema", certificate["schema"] == CERT_SCHEMA)
    core_hash = sha256_bytes(canonical_bytes(certificate["core"]))
    checked(
        "certificate.core_sha256",
        isinstance(certificate["core_sha256"], str)
        and HEX64_RE.fullmatch(certificate["core_sha256"]) is not None
        and certificate["core_sha256"] == core_hash,
    )
    checked(
        "certificate.run_id",
        certificate["run_id"] == "exp003-step3-" + core_hash[:24],
    )
    core = exact_keys(
        certificate["core"],
        {
            "schema",
            "arithmetic",
            "conventions",
            "assumptions",
            "source_sha256",
            "julia_version",
            "formal_noncommutative_derivation",
            "exact_cases",
            "negative_controls",
            "claim_classification",
        },
        "core",
    )
    checked("core.schema", core["schema"] == CORE_SCHEMA)
    checked("core.julia_version", core["julia_version"] == "1.12.6")
    checked("core.arithmetic", core["arithmetic"] == EXPECTED_ARITHMETIC)
    checked("core.conventions", core["conventions"] == EXPECTED_CONVENTIONS)
    checked("core.assumptions", core["assumptions"] == EXPECTED_ASSUMPTIONS)
    checked(
        "core.claim_classification",
        core["claim_classification"] == EXPECTED_CLASSIFICATION,
    )
    source_hashes = exact_keys(
        core["source_sha256"],
        {"discover_split_unsplit.jl", "exact_gaussian_matrix.jl"},
        "core.source_sha256",
    )
    checked(
        "core.source_hash_format",
        all(
            isinstance(digest, str) and HEX64_RE.fullmatch(digest)
            for digest in source_hashes.values()
        ),
    )
    if source_root is not None:
        for name, digest in source_hashes.items():
            checked(
                "core.source." + name,
                sha256_file(source_root / name) == digest,
            )

    verify_formal(core["formal_noncommutative_derivation"])
    expected_cases = [
        ("pauli_X_Z_half", "EXACT_IDENTITY_WITNESS"),
        ("pauli_X_Z_zero", "EXACT_EDGE_CASE"),
        ("pauli_X_Z_negative_two_thirds", "EXACT_EDGE_CASE"),
        ("commutative_scalar_one", "EXACT_COUNTEREXAMPLE"),
        ("linear_scaling_large_step", "EXACT_COUNTEREXAMPLE"),
    ]
    records = core["exact_cases"]
    ensure(
        isinstance(records, list) and len(records) == len(expected_cases),
        "core.exact_cases: expected exactly five cases",
    )
    cases = {}
    for index, (case_id, classification) in enumerate(expected_cases):
        parsed = verify_case(
            records[index], f"exact_cases[{index}]", case_id, classification
        )
        cases[case_id] = parsed

    checked(
        "cases.noncommuting",
        not is_zero(cases["pauli_X_Z_half"]["commutator"])
        and not is_zero(cases["pauli_X_Z_half"]["defect"]),
    )
    checked("cases.zero_step", is_zero(cases["pauli_X_Z_zero"]["defect"]))
    checked(
        "cases.negative_step",
        cases["pauli_X_Z_negative_two_thirds"]["alpha"] < 0
        and not is_zero(cases["pauli_X_Z_negative_two_thirds"]["defect"]),
    )
    verify_negative_controls(core["negative_controls"], cases)

    if receipt_path is not None:
        ensure(source_root is not None, "--receipt requires --source-root")
        verify_receipt(receipt_path, certificate_path, certificate, source_root)
    return certificate


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
    print(
        "BOUNDARY=exact finite certificate reconstructed; "
        "universal identity and norm bound remain Lean-only"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
