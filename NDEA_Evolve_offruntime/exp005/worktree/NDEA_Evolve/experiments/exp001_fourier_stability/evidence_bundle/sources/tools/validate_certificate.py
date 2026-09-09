#!/usr/bin/env python3
import hashlib
import json
import sys
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


def rational(item):
    return Fraction(int(item["numerator"]), int(item["denominator"]))


def complex_rational(item):
    return complex_fraction(rational(item["real"]), rational(item["imaginary"]))


class complex_fraction(tuple):
    __slots__ = ()

    def __new__(cls, real, imag):
        return tuple.__new__(cls, (real, imag))

    @property
    def real(self):
        return self[0]

    @property
    def imag(self):
        return self[1]

    def __add__(self, other):
        return complex_fraction(self.real + other.real, self.imag + other.imag)

    def __sub__(self, other):
        return complex_fraction(self.real - other.real, self.imag - other.imag)

    def __neg__(self):
        return complex_fraction(-self.real, -self.imag)

    def __mul__(self, other):
        return complex_fraction(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    def __truediv__(self, other):
        denominator = other.real * other.real + other.imag * other.imag
        if denominator == 0:
            raise ZeroDivisionError("exact complex division by zero")
        return complex_fraction(
            (self.real * other.real + self.imag * other.imag) / denominator,
            (self.imag * other.real - self.real * other.imag) / denominator,
        )

    def conjugate(self):
        return complex_fraction(self.real, -self.imag)

    def abs_squared(self):
        return self.real * self.real + self.imag * self.imag


ZERO_C = complex_fraction(Fraction(0), Fraction(0))
ONE_C = complex_fraction(Fraction(1), Fraction(0))
I_C = complex_fraction(Fraction(0), Fraction(1))


def laurent(entries):
    return {
        int(entry["exponent"]): rational(entry["coefficient"])
        for entry in entries
    }


def laurent_mul(left, right):
    result = {}
    for le, lc in left.items():
        for re, rc in right.items():
            exponent = le + re
            result[exponent] = result.get(exponent, Fraction(0)) + lc * rc
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def laurent_eval(poly, value):
    if value == 0 and any(exponent < 0 for exponent in poly):
        raise ZeroDivisionError("negative Laurent power at zero")
    return sum(
        (coefficient * value**exponent for exponent, coefficient in poly.items()),
        Fraction(0),
    )


def rational_poly(entries):
    degrees = [int(entry["degree"]) for entry in entries]
    if degrees != list(range(len(entries))):
        raise AssertionError(f"non-contiguous polynomial degrees: {degrees}")
    return [rational(entry["coefficient"]) for entry in entries]


def complex_poly(entries):
    degrees = [int(entry["degree"]) for entry in entries]
    if degrees != list(range(len(entries))):
        raise AssertionError(f"non-contiguous polynomial degrees: {degrees}")
    return [complex_rational(entry["coefficient"]) for entry in entries]


def trim_poly(poly, zero):
    result = list(poly)
    while len(result) > 1 and result[-1] == zero:
        result.pop()
    return result


def rational_poly_add(left, right):
    result = [Fraction(0)] * max(len(left), len(right))
    for index, coefficient in enumerate(left):
        result[index] += coefficient
    for index, coefficient in enumerate(right):
        result[index] += coefficient
    return trim_poly(result, Fraction(0))


def rational_poly_scale(scalar, poly):
    return trim_poly([scalar * coefficient for coefficient in poly], Fraction(0))


def complex_poly_mul(left, right):
    result = [ZERO_C for _ in range(len(left) + len(right) - 1)]
    for left_index, left_coefficient in enumerate(left):
        for right_index, right_coefficient in enumerate(right):
            result[left_index + right_index] = (
                result[left_index + right_index] + left_coefficient * right_coefficient
            )
    return trim_poly(result, ZERO_C)


def complex_poly_eval(poly, value):
    result = ZERO_C
    for coefficient in reversed(poly):
        result = result * value + coefficient
    return result


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: validate_certificate.py CERTIFICATE JULIA_SOURCE")
    certificate_path = Path(sys.argv[1])
    source_path = Path(sys.argv[2])
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))

    assert certificate["schema_version"] == "ndea-evolve.exp001.fourier-stability.v1"
    assert certificate["overall_status"] == "PASS"
    assert certificate["run"]["julia_version"] == "1.12.6"
    assert certificate["source_sha256"] == sha256(source_path)
    assert certificate["canonicalization"] == (
        "UTF-8 JSON with lexicographically sorted object keys, two-space indentation, "
        "and one trailing LF; nonintegral numeric observations are decimal strings"
    )

    # Recreate the exact canonical core serialized and hashed by Julia.  The core
    # intentionally stores nonintegral observations as strings, avoiding
    # cross-language floating-point rendering differences.
    canonical_core_object = dict(certificate)
    run = canonical_core_object.pop("run")
    canonical_core = (
        json.dumps(
            canonical_core_object,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
            separators=(",", ": "),
        )
        + "\n"
    ).encode("utf-8")
    reconstructed_core_sha256 = hashlib.sha256(canonical_core).hexdigest()
    assert run["core_certificate_sha256"] == reconstructed_core_sha256
    timestamp_digits = "".join(character for character in run["timestamp_utc"] if character.isdigit())
    assert len(timestamp_digits) >= 14
    assert run["run_id"] == (
        f"exp001-{reconstructed_core_sha256[:12]}-{timestamp_digits[:14]}"
    )

    operator = certificate["operator_derivation"]
    constructed = laurent(operator["constructed_laurent_symbol"])
    factor_left = laurent(operator["factor_left"])
    factor_right = laurent(operator["factor_right"])
    factor_product = laurent(operator["factorization_product"])
    expected_stencil = {-1: Fraction(-1), 0: Fraction(2), 1: Fraction(-1)}
    assert constructed == expected_stencil
    assert laurent_mul(factor_left, factor_right) == expected_stencil
    assert factor_product == expected_stencil
    assert operator["factorization_exact"] is True
    assert operator["derived_eigenvalue"] == "lambda_h(theta)=4*sin(theta/2)^2/h^2"

    half_angle = operator["half_angle_coefficient_certificate"]
    constant_two = rational_poly(half_angle["constant_two_polynomial"])
    cos_theta_as_s = rational_poly(half_angle["cos_theta_as_s_polynomial"])
    minus_two_cos = rational_poly(half_angle["minus_two_cos_theta_polynomial"])
    derived_half_angle = rational_poly(half_angle["derived_symbol_polynomial"])
    expected_half_angle = rational_poly(half_angle["expected_symbol_polynomial"])
    assert constant_two == [Fraction(2)]
    assert cos_theta_as_s == [Fraction(1), Fraction(0), Fraction(-2)]
    assert minus_two_cos == rational_poly_scale(Fraction(-2), cos_theta_as_s)
    assert derived_half_angle == rational_poly_add(constant_two, minus_two_cos)
    assert derived_half_angle == expected_half_angle == [Fraction(0), Fraction(0), Fraction(4)]
    assert half_angle["operation"] == "2+(-2)*(1-2*s^2)"
    assert half_angle["exact_coefficient_equality"] is True

    cayley = certificate["cayley_crank_nicolson_derivation"]
    scalar_equation = cayley["structured_scalar_equation"]
    solution = cayley["structured_solution"]
    equation_left = complex_poly(scalar_equation["left_factor_times_c_next"])
    equation_right = complex_poly(scalar_equation["right_factor_times_c_current"])
    solution_numerator = complex_poly(solution["amplification_numerator"])
    solution_denominator = complex_poly(solution["amplification_denominator"])
    expected_pminus = [ONE_C, -I_C]
    expected_pplus = [ONE_C, I_C]
    assert equation_left == expected_pplus
    assert equation_right == expected_pminus
    assert solution_numerator == equation_right
    assert solution_denominator == equation_left
    cross_left = complex_poly(solution["cross_multiplication_left"])
    cross_right = complex_poly(solution["cross_multiplication_right"])
    assert cross_left == complex_poly_mul(equation_left, solution_numerator)
    assert cross_right == complex_poly_mul(equation_right, solution_denominator)
    assert cross_left == cross_right
    assert solution["exact_coefficient_equality"] is True

    modulus = certificate["unit_modulus_certificate"]
    numerator = complex_poly(modulus["numerator_polynomial"])
    denominator = complex_poly(modulus["denominator_polynomial"])
    numerator_norm = complex_poly(modulus["numerator_times_conjugate"])
    denominator_norm = complex_poly(modulus["denominator_times_conjugate"])
    expected_norm = [
        complex_fraction(Fraction(1), Fraction(0)),
        ZERO_C,
        complex_fraction(Fraction(1), Fraction(0)),
    ]
    assert numerator == solution_numerator == expected_pminus
    assert denominator == solution_denominator == expected_pplus
    assert complex_poly_mul(numerator, [item.conjugate() for item in numerator]) == numerator_norm
    assert complex_poly_mul(denominator, [item.conjugate() for item in denominator]) == denominator_norm
    assert numerator_norm == expected_norm
    assert denominator_norm == expected_norm
    assert modulus["common_norm_squared"] == "1+a^2"
    assert modulus["exact_coefficient_equalities"] is True

    exact_samples = modulus["exact_rational_samples"]
    assert len(exact_samples) == 4
    expected_sample_parameters = {
        Fraction(-3, 2), Fraction(0), Fraction(5, 7), Fraction(11, 3)
    }
    assert {rational(sample["a"]) for sample in exact_samples} == expected_sample_parameters
    for sample in exact_samples:
        a = rational(sample["a"])
        amplification = complex_fraction(
            rational(sample["amplification_real"]),
            rational(sample["amplification_imaginary"]),
        )
        expected_amplification = complex_fraction(
            (1 - a * a) / (1 + a * a),
            (-2 * a) / (1 + a * a),
        )
        assert amplification == expected_amplification
        assert amplification.abs_squared() == Fraction(1)
        assert rational(sample["abs_squared"]) == Fraction(1)
        assert sample["status"] == "EXACT_RATIONAL_IDENTITY"

    checks = certificate["checks"]
    high_precision = checks["high_precision_periodic_modes"]
    assert high_precision["status"] == "PASS_FLOATING_POINT_EXPERIMENT"
    assert high_precision["precision_bits"] == 256
    assert high_precision["case_count"] == 4200
    assert Decimal(high_precision["max_periodicity_error"]) < Decimal(high_precision["tolerance"])
    assert Decimal(high_precision["max_eigen_residual"]) < Decimal(high_precision["tolerance"])
    assert Decimal(high_precision["max_modulus_squared_error"]) < Decimal(high_precision["tolerance"])

    random_search = checks["fixed_seed_random_search"]
    assert random_search["status"] == "PASS_FLOAT64_COUNTEREXAMPLE_SEARCH"
    assert random_search["case_count"] == 256
    assert random_search["seed"] == run["rng_seed"] == 0x4E444541
    assert Decimal(random_search["max_mixed_bound_ratio"]) <= Decimal(1)
    assert Decimal(random_search["max_modulus_squared_error"]) < Decimal("5e-13")
    assert Decimal(random_search["max_periodicity_error"]) < Decimal("5e-13")

    edge_cases = {item["case"]: item for item in checks["edge_cases"]}
    assert edge_cases["constant mode theta=0"]["status"] == "STANDARD_ANALYTIC_SPECIAL_VALUE"
    assert edge_cases["Nyquist mode theta=pi"]["status"] == "STANDARD_ANALYTIC_SPECIAL_VALUE"
    assert edge_cases["k=0"]["status"] == "STANDARD_ANALYTIC_SPECIAL_VALUE"
    assert edge_cases["h=0"]["status"] == "GUARD_REJECTED"

    adversarial = checks["adversarial_counterexamples"]
    assert len(adversarial) == 5
    assert all(item["counterexample_found"] is True for item in adversarial)
    adversarial_by_id = {item["id"]: item for item in adversarial}
    assert set(adversarial_by_id) == {
        "ADV_WRONG_EIGENVALUE_ARGUMENT",
        "ADV_REVERSED_STENCIL_SIGN",
        "ADV_WRONG_CAYLEY_NUMERATOR",
        "ADV_DROP_REAL_PARAMETER",
        "ADV_ZERO_GRID_SPACING",
    }

    wrong_eigen = adversarial_by_id["ADV_WRONG_EIGENVALUE_ARGUMENT"]
    assert wrong_eigen["status"] == "EXACT_LAURENT_EVALUATION_COUNTEREXAMPLE"
    wrong_eigen_correct_symbol = laurent(wrong_eigen["correct_symbol"])
    wrong_eigen_altered_symbol = laurent(wrong_eigen["altered_symbol"])
    wrong_eigen_witness = wrong_eigen["witness"]
    witness_z = rational(wrong_eigen_witness["z"])
    assert witness_z == Fraction(-1)
    assert rational(wrong_eigen_witness["h"]) == Fraction(1)
    assert wrong_eigen_correct_symbol == expected_stencil
    assert wrong_eigen_altered_symbol == {
        -2: Fraction(-1), 0: Fraction(2), 2: Fraction(-1)
    }
    assert laurent_eval(wrong_eigen_correct_symbol, witness_z) == rational(
        wrong_eigen_witness["correct_value"]
    ) == Fraction(4)
    assert laurent_eval(wrong_eigen_altered_symbol, witness_z) == rational(
        wrong_eigen_witness["wrong_value"]
    ) == Fraction(0)

    reversed_sign = adversarial_by_id["ADV_REVERSED_STENCIL_SIGN"]
    assert reversed_sign["status"] == "EXACT_COEFFICIENT_MISMATCH"
    assert laurent(reversed_sign["derived"]) == expected_stencil
    assert laurent(reversed_sign["altered"]) == {
        exponent: -coefficient for exponent, coefficient in expected_stencil.items()
    }

    wrong_cayley = adversarial_by_id["ADV_WRONG_CAYLEY_NUMERATOR"]
    assert wrong_cayley["status"] == "EXACT_RATIONAL_COUNTEREXAMPLE"
    wrong_numerator = complex_poly(wrong_cayley["wrong_numerator_polynomial"])
    wrong_numerator_norm = complex_poly(wrong_cayley["wrong_numerator_norm_polynomial"])
    assert wrong_numerator == [ONE_C, complex_fraction(Fraction(-1), Fraction(0))]
    assert complex_poly_mul(
        wrong_numerator, [item.conjugate() for item in wrong_numerator]
    ) == wrong_numerator_norm
    assert wrong_numerator_norm == [
        ONE_C,
        complex_fraction(Fraction(-2), Fraction(0)),
        ONE_C,
    ]
    assert complex_poly(wrong_cayley["correct_denominator_norm_polynomial"]) == denominator_norm
    wrong_cayley_a = rational(wrong_cayley["witness"]["a"])
    wrong_cayley_amplification = complex_poly_eval(
        wrong_numerator, complex_fraction(wrong_cayley_a, Fraction(0))
    ) / complex_poly_eval(denominator, complex_fraction(wrong_cayley_a, Fraction(0)))
    assert wrong_cayley_a == Fraction(1)
    assert wrong_cayley_amplification.abs_squared() == rational(
        wrong_cayley["witness"]["modulus_squared"]
    ) == Fraction(0)

    nonreal = adversarial_by_id["ADV_DROP_REAL_PARAMETER"]
    assert nonreal["status"] == "EXACT_GAUSSIAN_RATIONAL_COUNTEREXAMPLE"
    nonreal_a = complex_rational(nonreal["witness"]["a"])
    nonreal_amplification = complex_rational(nonreal["witness"]["amplification"])
    assert nonreal_a == complex_fraction(Fraction(0), Fraction(1, 2))
    reconstructed_nonreal_amplification = (
        ONE_C - I_C * nonreal_a
    ) / (ONE_C + I_C * nonreal_a)
    assert nonreal_amplification == reconstructed_nonreal_amplification == complex_fraction(
        Fraction(3), Fraction(0)
    )
    assert nonreal_amplification.abs_squared() == rational(
        nonreal["witness"]["modulus_squared"]
    ) == Fraction(9)

    zero_spacing = adversarial_by_id["ADV_ZERO_GRID_SPACING"]
    assert zero_spacing["status"] == "DOMAIN_GUARD_REJECTION"
    assert rational(zero_spacing["witness"]["h"]) == Fraction(0)
    assert zero_spacing["witness"]["result"] == "DomainError"

    trust = certificate["trust_boundary"]
    assert trust["julia_boolean_trusted_by_lean"] is False
    assert trust["certificate_parsed_by_lean"] is False
    assert trust["lean_rederives_general_theorems"] is True

    print(f"certificate={certificate_path}")
    print(f"certificate_sha256={sha256(certificate_path)}")
    print(f"julia_source_sha256={sha256(source_path)}")
    print("json_parse=PASS")
    print("laurent_stencil_reconstruction=PASS")
    print("laurent_factorization_reconstruction=PASS")
    print("half_angle_coefficient_reconstruction=PASS")
    print("cayley_scalar_cross_multiplication=PASS")
    print("cayley_norm_polynomial_reconstruction=PASS")
    print("exact_cayley_samples_reconstruction=PASS_4_OF_4")
    print("numerical_bounds_schema=PASS")
    print("adversarial_witness_reconstruction=PASS_5_OF_5")
    print(f"canonical_core_sha256={reconstructed_core_sha256}")
    print("canonical_core_hash_reconstruction=PASS")
    print("trust_boundary=LEAN_DOES_NOT_TRUST_JULIA_BOOLEAN")
    print("CERTIFICATE_VALIDATION_STATUS=PASS")


if __name__ == "__main__":
    main()
