#!/usr/bin/env julia

include(joinpath(@__DIR__, "exact_gaussian_matrix.jl"))
using .ExactGaussianMatrix
using Dates

const I_G = g(0, 1)
const EXP_ROOT = normpath(joinpath(@__DIR__, "..", ".."))
const Word = Tuple
const NCPoly = Dict{Word,Q}

function assert_zero(label::AbstractString, matrix::Matrix{G})
    is_zero_matrix(matrix) || error("$label is not zero: $matrix")
end

function mul_chain(first::Matrix{G}, rest::Matrix{G}...)
    result = first
    for factor in rest
        result = mat_mul(result, factor)
    end
    result
end

function cayley_data(H::Matrix{G}, alpha::Q)
    rows, columns = size(H)
    rows == columns || error("Cayley input must be square")
    is_hermitian_exact(H) || error("Hermitian assumption failed")
    identity = eye_g(rows)
    skew = mat_scale(I_G * gq(alpha), H)
    denominator = mat_add(identity, skew)
    numerator = mat_sub(identity, skew)
    resolvent, trace = inverse_with_trace(denominator)
    resolvent === nothing && error("Hermitian Cayley denominator is singular")
    factor = mat_mul(numerator, resolvent)
    assert_zero("denominator right inverse",
                mat_sub(mat_mul(denominator, resolvent), identity))
    assert_zero("denominator left inverse",
                mat_sub(mat_mul(resolvent, denominator), identity))
    (H=H, skew=skew, D=denominator, N=numerator, R=resolvent,
     C=factor, trace=trace)
end

function local_case(id::String, classification::String,
                    A::Matrix{G}, B::Matrix{G}, alpha::Q)
    size(A) == size(B) || error("A and B dimensions differ")
    n, m = size(A)
    n == m || error("A and B must be square")
    is_hermitian_exact(A) || error("A is not Hermitian")
    is_hermitian_exact(B) || error("B is not Hermitian")
    sum_generator = mat_add(A, B)
    data_A = cayley_data(A, alpha)
    data_B = cayley_data(B, alpha)
    data_sum = cayley_data(sum_generator, alpha)
    identity = eye_g(n)

    split_product = mat_mul(data_A.C, data_B.C)
    local_defect = mat_sub(split_product, data_sum.C)
    first_term = mul_chain(data_sum.R, B, A, data_A.R, data_B.R)
    second_term = mul_chain(A, data_A.R, B, data_B.R)
    coefficient = q(2) * alpha * alpha
    factorized_rhs = mat_scale(gq(coefficient), mat_sub(first_term, second_term))
    identity_residual = mat_sub(local_defect, factorized_rhs)
    assert_zero("$id exact split-versus-unsplit identity", identity_residual)

    commutator = mat_sub(mat_mul(A, B), mat_mul(B, A))
    residuals = Dict(
        "A_hermitian" => mat_sub(mat_dagger(A), A),
        "B_hermitian" => mat_sub(mat_dagger(B), B),
        "sum_hermitian" => mat_sub(mat_dagger(sum_generator), sum_generator),
        "sum_definition" => mat_sub(sum_generator, mat_add(A, B)),
        "D_A_R_A_minus_I" => mat_sub(mat_mul(data_A.D, data_A.R), identity),
        "R_A_D_A_minus_I" => mat_sub(mat_mul(data_A.R, data_A.D), identity),
        "D_B_R_B_minus_I" => mat_sub(mat_mul(data_B.D, data_B.R), identity),
        "R_B_D_B_minus_I" => mat_sub(mat_mul(data_B.R, data_B.D), identity),
        "D_sum_R_sum_minus_I" => mat_sub(mat_mul(data_sum.D, data_sum.R), identity),
        "R_sum_D_sum_minus_I" => mat_sub(mat_mul(data_sum.R, data_sum.D), identity),
        "C_A_minus_N_A_R_A" => mat_sub(data_A.C, mat_mul(data_A.N, data_A.R)),
        "C_B_minus_N_B_R_B" => mat_sub(data_B.C, mat_mul(data_B.N, data_B.R)),
        "C_sum_minus_N_sum_R_sum" => mat_sub(data_sum.C, mat_mul(data_sum.N, data_sum.R)),
        "split_minus_C_A_C_B" => mat_sub(split_product, mat_mul(data_A.C, data_B.C)),
        "local_defect_definition" =>
            mat_sub(local_defect, mat_sub(split_product, data_sum.C)),
        "factorized_rhs_definition" =>
            mat_sub(factorized_rhs,
                    mat_scale(gq(coefficient), mat_sub(first_term, second_term))),
        "exact_identity" => identity_residual,
    )
    for (label, residual) in residuals
        assert_zero("$id residual $label", residual)
    end

    record = Dict(
        "id" => id,
        "classification" => classification,
        "dimension" => n,
        "alpha" => rational_json(alpha),
        "A" => matrix_json(A),
        "B" => matrix_json(B),
        "A_plus_B" => matrix_json(sum_generator),
        "D_A" => matrix_json(data_A.D),
        "D_B" => matrix_json(data_B.D),
        "D_sum" => matrix_json(data_sum.D),
        "N_A" => matrix_json(data_A.N),
        "N_B" => matrix_json(data_B.N),
        "N_sum" => matrix_json(data_sum.N),
        "R_A" => matrix_json(data_A.R),
        "R_B" => matrix_json(data_B.R),
        "R_sum" => matrix_json(data_sum.R),
        "C_A" => matrix_json(data_A.C),
        "C_B" => matrix_json(data_B.C),
        "C_sum" => matrix_json(data_sum.C),
        "split_product" => matrix_json(split_product),
        "local_defect" => matrix_json(local_defect),
        "rhs_first_term" => matrix_json(first_term),
        "rhs_second_term" => matrix_json(second_term),
        "factorized_rhs" => matrix_json(factorized_rhs),
        "coefficient" => rational_json(coefficient),
        "generator_commutator" => matrix_json(commutator),
        "generators_commute" => is_zero_matrix(commutator),
        "local_defect_zero" => is_zero_matrix(local_defect),
        "pivot_traces" => Dict("A" => data_A.trace, "B" => data_B.trace,
                               "sum" => data_sum.trace),
        "residuals" => Dict(key => matrix_json(value)
                            for (key, value) in residuals),
    )
    record, (alpha=alpha, A=A, B=B, sum=sum_generator, defect=local_defect,
             commutator=commutator)
end

function nc_clean(poly::NCPoly)
    NCPoly(word => coefficient for (word, coefficient) in poly
           if !iszero(coefficient))
end

nc_constant(coefficient::Q) =
    iszero(coefficient) ? NCPoly() : NCPoly(() => coefficient)
nc_variable(name::String) = NCPoly((name,) => q(1))

function nc_add(left::NCPoly, right::NCPoly)
    result = copy(left)
    for (word, coefficient) in right
        result[word] = get(result, word, q(0)) + coefficient
    end
    nc_clean(result)
end

nc_neg(poly::NCPoly) = NCPoly(word => -coefficient
                              for (word, coefficient) in poly)
nc_sub(left::NCPoly, right::NCPoly) = nc_add(left, nc_neg(right))
nc_scale(coefficient::Q, poly::NCPoly) =
    nc_clean(NCPoly(word => coefficient * value for (word, value) in poly))

function nc_mul(left::NCPoly, right::NCPoly)
    result = NCPoly()
    for (left_word, left_coefficient) in left
        for (right_word, right_coefficient) in right
            word = (left_word..., right_word...)
            result[word] = get(result, word, q(0)) +
                           left_coefficient * right_coefficient
        end
    end
    nc_clean(result)
end

function nc_product(first::NCPoly, rest::NCPoly...)
    result = first
    for factor in rest
        result = nc_mul(result, factor)
    end
    result
end

function nc_json(poly::NCPoly)
    words = sort!(collect(keys(poly)); by=word -> (length(word), join(word, "\0")))
    [Dict("coefficient" => rational_json(poly[word]),
          "word" => collect(word)) for word in words]
end

function formal_derivation()
    one = nc_constant(q(1))
    X, Y = nc_variable("X"), nc_variable("Y")
    RA, RB, RS = nc_variable("R_A"), nc_variable("R_B"), nc_variable("R_sum")
    DA = nc_add(one, X)
    DB = nc_add(one, Y)
    DS = nc_add(nc_add(one, X), Y)
    NA = nc_sub(one, X)
    NB = nc_sub(one, Y)
    NS = nc_sub(nc_sub(one, X), Y)

    original_A = nc_mul(NA, RA)
    original_B = nc_mul(NB, RB)
    original_sum = nc_mul(NS, RS)
    affine_A = nc_sub(nc_scale(q(2), RA), one)
    affine_B = nc_sub(nc_scale(q(2), RB), one)
    affine_sum = nc_sub(nc_scale(q(2), RS), one)
    original_defect = nc_sub(nc_mul(original_A, original_B), original_sum)
    affine_defect = nc_sub(nc_mul(affine_A, affine_B), affine_sum)

    first_original = nc_product(X, RA, Y, RB)
    first_after_X = nc_product(nc_sub(one, RA), Y, RB)
    first_reduced = nc_mul(nc_sub(one, RA), nc_sub(one, RB))

    product_gap = nc_sub(nc_mul(DB, DA), DS)
    product_gap_expanded = nc_mul(Y, X)
    bridge_context = nc_product(RS, product_gap, RA, RB)
    bridge_expanded = nc_product(RS, Y, X, RA, RB)
    product_context = nc_product(RS, DB, DA, RA, RB)
    sum_context = nc_product(RS, DS, RA, RB)
    bridge_reduced = nc_sub(RS, nc_mul(RA, RB))

    target_original = nc_scale(q(2), nc_sub(first_original, bridge_expanded))
    target_reduced = nc_scale(q(2), nc_sub(first_reduced, bridge_reduced))
    final_residual = nc_sub(affine_defect, target_reduced)
    isempty(final_residual) || error("formal noncommutative residual is nonzero")
    product_gap == product_gap_expanded || error("denominator product gap mismatch")
    bridge_context == bridge_expanded || error("bridge expansion mismatch")

    relation(id, lhs, rhs) =
        Dict("id" => id, "lhs" => nc_json(lhs), "rhs" => nc_json(rhs))
    Dict(
        "symbols" => Dict(
            "X" => "i*alpha*A",
            "Y" => "i*alpha*B",
            "R_A" => "(1+X)^-1",
            "R_B" => "(1+Y)^-1",
            "R_sum" => "(1+X+Y)^-1",
            "multiplication" => "noncommutative; coefficients are central rationals",
        ),
        "right_inverse_relations" => [
            relation("D_A_R_A", nc_mul(DA, RA), one),
            relation("D_B_R_B", nc_mul(DB, RB), one),
            relation("D_sum_R_sum", nc_mul(DS, RS), one),
        ],
        "left_inverse_relations" => [
            relation("R_A_D_A", nc_mul(RA, DA), one),
            relation("R_B_D_B", nc_mul(RB, DB), one),
            relation("R_sum_D_sum", nc_mul(RS, DS), one),
        ],
        "cayley_affine_reductions" => [
            Dict("id" => "A", "original" => nc_json(original_A),
                 "reduced" => nc_json(affine_A), "uses" => ["D_A_R_A"]),
            Dict("id" => "B", "original" => nc_json(original_B),
                 "reduced" => nc_json(affine_B), "uses" => ["D_B_R_B"]),
            Dict("id" => "sum", "original" => nc_json(original_sum),
                 "reduced" => nc_json(affine_sum), "uses" => ["D_sum_R_sum"]),
        ],
        "original_defect" => nc_json(original_defect),
        "affine_defect_expression" => nc_json(affine_defect),
        "affine_defect_expanded" => nc_json(affine_defect),
        "first_rhs_term_reduction" => Dict(
            "original" => nc_json(first_original),
            "after_X_R_A" => nc_json(first_after_X),
            "reduced" => nc_json(first_reduced),
            "uses" => ["D_A_R_A", "D_B_R_B"],
        ),
        "denominator_product_gap" => Dict(
            "expression" => nc_json(product_gap),
            "expanded" => nc_json(product_gap_expanded),
            "residual" => nc_json(nc_sub(product_gap, product_gap_expanded)),
        ),
        "resolvent_bridge" => Dict(
            "gap_context" => nc_json(bridge_context),
            "expanded" => nc_json(bridge_expanded),
            "product_context" => nc_json(product_context),
            "product_context_reduced" => nc_json(RS),
            "sum_context" => nc_json(sum_context),
            "sum_context_reduced" => nc_json(nc_mul(RA, RB)),
            "reduced" => nc_json(bridge_reduced),
            "uses" => ["D_A_R_A", "D_B_R_B", "R_sum_D_sum"],
        ),
        "scaled_target_original" => nc_json(target_original),
        "scaled_target_reduced" => nc_json(target_reduced),
        "final_residual" => nc_json(final_residual),
        "rewrite_trace" => [
            "replace each Cayley factor (1-X)R by 2R-1 using its right inverse law",
            "expand the split-minus-unsplit defect without commuting any symbols",
            "reduce X*R_A and Y*R_B to 1-R_A and 1-R_B",
            "expand (1+Y)(1+X)-(1+X+Y) to Y*X",
            "sandwich that gap by R_sum on the left and R_A*R_B on the right",
            "cancel only adjacent certified inverse pairs to obtain R_sum-R_A*R_B",
            "the reduced target equals the expanded defect exactly",
            "substitute X=i*alpha*A and Y=i*alpha*B, so i^2=-1 yields the stated 2*alpha^2 formula",
        ],
    )
end

pauli_X = G[g(0) g(1); g(1) g(0)]
pauli_Z = G[g(1) g(0); g(0) g(-1)]
scalar_one = reshape(G[g(1)], 1, 1)
scalar_tenth = reshape(G[gq(q(1, 10))], 1, 1)

case_noncommuting, raw_noncommuting = local_case(
    "pauli_X_Z_half", "EXACT_IDENTITY_WITNESS", pauli_X, pauli_Z, q(1, 2))
case_zero, raw_zero = local_case(
    "pauli_X_Z_zero", "EXACT_EDGE_CASE", pauli_X, pauli_Z, q(0))
case_negative, raw_negative = local_case(
    "pauli_X_Z_negative_two_thirds", "EXACT_EDGE_CASE", pauli_X, pauli_Z, q(-2, 3))
case_commutative, raw_commutative = local_case(
    "commutative_scalar_one", "EXACT_COUNTEREXAMPLE", scalar_one, scalar_one, q(1))
case_linear, raw_linear = local_case(
    "linear_scaling_large_step", "EXACT_COUNTEREXAMPLE",
    scalar_tenth, scalar_tenth, q(10))

is_zero_matrix(raw_noncommuting.commutator) &&
    error("noncommuting witness unexpectedly commutes")
is_zero_matrix(raw_noncommuting.defect) &&
    error("noncommuting witness unexpectedly has zero local defect")
is_zero_matrix(raw_zero.defect) || error("zero-step defect is nonzero")
is_zero_matrix(raw_negative.defect) &&
    error("negative-step witness unexpectedly has zero local defect")
is_zero_matrix(raw_commutative.commutator) ||
    error("commutative-collapse witness does not commute")
is_zero_matrix(raw_commutative.defect) &&
    error("commutative-collapse witness unexpectedly has zero defect")

linear_defect_scalar = raw_linear.defect[1, 1]
linear_defect_modulus_sq_g = conj(linear_defect_scalar) * linear_defect_scalar
iszero(imag(linear_defect_modulus_sq_g)) || error("modulus square is not real")
linear_defect_modulus_sq = real(linear_defect_modulus_sq_g)
linear_A_norm = abs(real(raw_linear.A[1, 1]))
linear_B_norm = abs(real(raw_linear.B[1, 1]))
linear_claimed_rhs = q(4) * abs(raw_linear.alpha) * linear_A_norm * linear_B_norm
linear_claimed_rhs_sq = linear_claimed_rhs * linear_claimed_rhs
linear_defect_modulus_sq > linear_claimed_rhs_sq ||
    error("large-step linear-scaling witness does not violate the false bound")
linear_defect_modulus_sq == q(4, 5) || error("unexpected defect modulus square")
linear_claimed_rhs == q(2, 5) || error("unexpected false-bound right side")

source_hashes = Dict(
    "discover_split_unsplit.jl" => sha256_file(@__FILE__),
    "exact_gaussian_matrix.jl" =>
        sha256_file(joinpath(@__DIR__, "exact_gaussian_matrix.jl")),
)

core = Dict(
    "schema" => "ndea.exp003.step3.split_unsplit_core.v1",
    "arithmetic" => Dict(
        "field" => "Gaussian rationals Q(i)",
        "rational_encoding" =>
            "normalized decimal numerator and positive denominator strings",
        "matrix_orientation" => "row-major JSON; column-vector action",
        "exact_algorithms" => [
            "manual matrix multiplication",
            "deterministic first-nonzero-pivot Gauss-Jordan",
            "free noncommutative word-polynomial expansion",
        ],
        "forbidden_in_exact_layer" => [
            "floating point", "LinearAlgebra.inv", "backslash solve",
            "numerical matrix norm",
        ],
    ),
    "conventions" => Dict(
        "D" => "I+i*alpha*H",
        "N" => "I-i*alpha*H",
        "R" => "D^-1",
        "C" => "N*R",
        "split_order" => "C_alpha(A)*C_alpha(B); B acts first on column vectors",
        "local_defect" => "C_alpha(A)*C_alpha(B)-C_alpha(A+B)",
        "exact_rhs" =>
            "2*alpha^2*(R_sum*B*A*R_A*R_B-A*R_A*B*R_B)",
    ),
    "assumptions" => [
        "finite square complex matrices",
        "A and B Hermitian",
        "alpha real, including zero and negative values",
    ],
    "source_sha256" => source_hashes,
    "julia_version" => string(VERSION),
    "formal_noncommutative_derivation" => formal_derivation(),
    "exact_cases" => [case_noncommuting, case_zero, case_negative,
                      case_commutative, case_linear],
    "negative_controls" => Dict(
        "commutative_collapse" => Dict(
            "case_id" => "commutative_scalar_one",
            "generators_commute" => true,
            "local_defect_nonzero" => true,
        ),
        "linear_scaling_large_step" => Dict(
            "case_id" => "linear_scaling_large_step",
            "statement_refuted" =>
                "norm(E_local(alpha)) <= 4*abs(alpha)*norm(Ahat)*norm(Bhat)",
            "norm_semantics" =>
                "Euclidean induced operator norm; for a 1x1 scalar matrix this is complex modulus",
            "alpha" => rational_json(raw_linear.alpha),
            "A_operator_norm" => rational_json(linear_A_norm),
            "B_operator_norm" => rational_json(linear_B_norm),
            "local_defect_modulus_squared" =>
                rational_json(linear_defect_modulus_sq),
            "claimed_rhs" => rational_json(linear_claimed_rhs),
            "claimed_rhs_squared" => rational_json(linear_claimed_rhs_sq),
            "strict_violation" => true,
            "scope_note" =>
                "A small-step witness is impossible because alpha^2 <= abs(alpha) for abs(alpha) <= 1",
        ),
    ),
    "claim_classification" => Dict(
        "exactly_derived_by_julia" => [
            "five Gaussian-rational matrix instances",
            "all Cayley inverses and identity residuals",
            "the split-versus-unsplit factorization residuals",
            "a free noncommutative algebra expansion",
            "commutative-collapse and corrected large-step linear-bound witnesses",
        ],
        "formally_verified_by_lean" =>
            "not supplied by this certificate; universal identity and operator-norm bound remain Lean-only",
        "not_claimed" => [
            "floating-point evidence", "infinite-dimensional operators",
            "telescoping", "continuous-exponential comparison",
        ],
    ),
)

core_bytes = Vector{UInt8}(codeunits(canonical_json(core)))
core_sha256 = sha256_hex(core_bytes)
run_id = "exp003-step3-" * core_sha256[1:24]
certificate = Dict(
    "schema" => "ndea.exp003.step3.split_unsplit_certificate.v1",
    "core" => core,
    "core_sha256" => core_sha256,
    "run_id" => run_id,
)

certificate_directory = joinpath(EXP_ROOT, "certificates")
metadata_directory = joinpath(EXP_ROOT, "metadata")
mkpath(certificate_directory)
mkpath(metadata_directory)
certificate_path = joinpath(certificate_directory, "split_unsplit_core.json")
open(certificate_path, "w") do stream
    write(stream, canonical_json(certificate), "\n")
end

receipt = Dict(
    "schema" => "ndea.exp003.step3.split_unsplit_run_receipt.v1",
    "run_id" => run_id,
    "core_sha256" => core_sha256,
    "certificate_path" => "certificates/split_unsplit_core.json",
    "certificate_sha256" => sha256_file(certificate_path),
    "source_sha256" => source_hashes,
    "julia_version" => string(VERSION),
    "timestamp_utc" => Dates.format(now(UTC), dateformat"yyyy-mm-ddTHH:MM:SS.sssZ"),
    "exact_case_count" => 5,
    "exact_status" => "PASS",
    "numeric_layer" => "ABSENT_BY_DESIGN",
)
receipt_path = joinpath(metadata_directory, "split_unsplit_run_receipt.json")
open(receipt_path, "w") do stream
    write(stream, canonical_json(receipt), "\n")
end

println("RUN_ID=", run_id)
println("CORE_SHA256=", core_sha256)
println("CERTIFICATE_SHA256=", sha256_file(certificate_path))
println("SOURCE_DISCOVERY_SHA256=", source_hashes["discover_split_unsplit.jl"])
println("SOURCE_LIBRARY_SHA256=", source_hashes["exact_gaussian_matrix.jl"])
println("EXACT_CASES=5")
println("NONCOMMUTING_IDENTITY=PASS")
println("ZERO_STEP_IDENTITY=PASS")
println("NEGATIVE_STEP_IDENTITY=PASS")
println("COMMUTATIVE_COLLAPSE_COUNTEREXAMPLE=PASS")
println("LINEAR_SCALING_LARGE_STEP_COUNTEREXAMPLE=PASS")
println("FORMAL_NONCOMMUTATIVE_EXPANSION=PASS")
println("JULIA_DISCOVERY_STATUS=PASS")
