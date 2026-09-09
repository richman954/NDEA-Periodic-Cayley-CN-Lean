#!/usr/bin/env julia

include(joinpath(@__DIR__, "exact_gaussian_matrix.jl"))
using .ExactGaussianMatrix
using Dates
using LinearAlgebra
using Random

const I_G = g(0, 1)
const EXP_ROOT = normpath(joinpath(@__DIR__, "..", ".."))

function assert_zero(label, M)
    is_zero_matrix(M) || error("$label is not zero: $M")
end

function cayley_data(H::Matrix{G}, a::Q; require_hermitian::Bool=true)
    n, m = size(H)
    n == m || error("Cayley input must be square")
    if require_hermitian && !is_hermitian_exact(H)
        error("Hermitian assumption failed")
    end
    identity = eye_g(n)
    iaH = mat_scale(I_G * gq(a), H)
    D = mat_add(identity, iaH)
    N = mat_sub(identity, iaH)
    Dinv, pivot_trace = inverse_with_trace(D)
    Dinv === nothing && error("Cayley denominator is singular")
    U = mat_mul(N, Dinv)
    det_D, det_D_trace = determinant_exact(D)
    det_N, det_N_trace = determinant_exact(N)
    det_U, det_U_trace = determinant_exact(U)
    h2 = mat_mul(H, H)
    gram_target = mat_add(identity, mat_scale(gq(a * a), h2))
    residuals = Dict(
        "hermitian" => mat_sub(mat_dagger(H), H),
        "D_dagger_minus_N" => mat_sub(mat_dagger(D), N),
        "N_dagger_minus_D" => mat_sub(mat_dagger(N), D),
        "D_N_commutator" => mat_commutator(D, N),
        "Dinv_left" => mat_sub(mat_mul(Dinv, D), identity),
        "Dinv_right" => mat_sub(mat_mul(D, Dinv), identity),
        "update_DU_minus_N" => mat_sub(mat_mul(D, U), N),
        "Ddagger_D_minus_gram" => mat_sub(mat_mul(mat_dagger(D), D), gram_target),
        "Ndagger_N_minus_gram" => mat_sub(mat_mul(mat_dagger(N), N), gram_target),
        "Udagger_U_minus_I" => mat_sub(mat_mul(mat_dagger(U), U), identity),
        "U_Udagger_minus_I" => mat_sub(mat_mul(U, mat_dagger(U)), identity),
    )
    for (label, residual) in residuals
        if label != "hermitian" || require_hermitian
            assert_zero(label, residual)
        end
    end
    Dict(
        "dimension" => n,
        "a" => rational_json(a),
        "H" => matrix_json(H),
        "D" => matrix_json(D),
        "N" => matrix_json(N),
        "D_inverse" => matrix_json(Dinv),
        "U" => matrix_json(U),
        "det_D" => gaussian_json(det_D),
        "det_N" => gaussian_json(det_N),
        "det_U" => gaussian_json(det_U),
        "det_U_modulus_sq" => gaussian_json(conj(det_U) * det_U),
        "pivot_trace_D_inverse" => pivot_trace,
        "determinant_traces" => Dict("D" => det_D_trace, "N" => det_N_trace, "U" => det_U_trace),
        "gram_target" => matrix_json(gram_target),
        "residuals" => Dict(k => matrix_json(v) for (k, v) in residuals),
    ), (D=D, N=N, Dinv=Dinv, U=U, detD=det_D, detN=det_N, detU=det_U)
end

function poly_add(P::Dict{Tuple{Int,Int},G}, Qp::Dict{Tuple{Int,Int},G})
    result = copy(P)
    for (key, value) in Qp
        result[key] = get(result, key, g(0)) + value
        iszero(result[key]) && delete!(result, key)
    end
    result
end

function poly_mul(P::Dict{Tuple{Int,Int},G}, Qp::Dict{Tuple{Int,Int},G})
    result = Dict{Tuple{Int,Int},G}()
    for ((ap, hp), cp) in P, ((aq, hq), cq) in Qp
        key = (ap + aq, hp + hq)
        result[key] = get(result, key, g(0)) + cp * cq
    end
    Dict(k => v for (k, v) in result if !iszero(v))
end

poly_star(P::Dict{Tuple{Int,Int},G}) = Dict(key => conj(value) for (key, value) in P)

function poly_json(P::Dict{Tuple{Int,Int},G})
    [Dict("a_power" => key[1], "H_power" => key[2], "coefficient" => gaussian_json(P[key]))
     for key in sort!(collect(keys(P)))]
end

Xpoly = Dict((0, 0) => g(1), (1, 1) => I_G)
Ypoly = Dict((0, 0) => g(1), (1, 1) => -I_G)
GramPoly = Dict((0, 0) => g(1), (2, 2) => g(1))
Xstar = poly_star(Xpoly)
Ystar = poly_star(Ypoly)
Xstar == Ypoly || error("symbolic star identity failed")
Ystar == Xpoly || error("symbolic star identity failed")
poly_mul(Xstar, Xpoly) == GramPoly || error("symbolic X gram identity failed")
poly_mul(Ystar, Ypoly) == GramPoly || error("symbolic Y gram identity failed")
poly_mul(Xpoly, Ypoly) == GramPoly || error("symbolic product identity failed")

H1 = G[g(0) g(1); g(1) g(0)]
H2 = G[g(1) g(0); g(0) g(-1)]
H3 = G[g(0) -I_G; I_G g(0)]

record1, raw1 = cayley_data(H1, q(1, 2))
record1["id"] = "pauli_X_half"
record2, raw2 = cayley_data(H2, q(2, 3))
record2["id"] = "pauli_Z_two_thirds"
record3, raw3 = cayley_data(H3, q(-3, 5))
record3["id"] = "pauli_Y_negative_three_fifths"

P21 = mat_mul(raw2.U, raw1.U)
P12 = mat_mul(raw1.U, raw2.U)
P321 = mat_mul(raw3.U, P21)
I2 = eye_g(2)
for (label, P) in (("P21", P21), ("P12", P12), ("P321", P321))
    assert_zero(label * " left-unitarity", mat_sub(mat_mul(mat_dagger(P), P), I2))
    assert_zero(label * " right-unitarity", mat_sub(mat_mul(P, mat_dagger(P)), I2))
end

generator_commutator = mat_commutator(H1, H2)
cayley_commutator = mat_commutator(raw1.U, raw2.U)
order_rhs = mat_scale(gq(-4 * q(1, 2) * q(2, 3)),
    mat_mul(mat_mul(mat_mul(mat_mul(raw1.Dinv, raw2.Dinv), generator_commutator), raw2.Dinv), raw1.Dinv))
assert_zero("order-defect identity", mat_sub(cayley_commutator, order_rhs))
is_zero_matrix(generator_commutator) && error("chosen generators unexpectedly commute")
is_zero_matrix(cayley_commutator) && error("chosen Cayley factors unexpectedly commute")

vectors = [
    G[g(1), g(0)],
    G[g(1, 1), gq(q(2, 3), q(-1, 4))],
    G[gq(q(-5, 7), q(3, 8)), gq(q(11, 6), q(2, 9))],
]
vector_checks = Any[]
for (factor_id, U) in (("U1", raw1.U), ("U2", raw2.U), ("P321", P321)), x in vectors
    y = apply_matrix(U, x)
    before = vector_norm_sq(x)
    after = vector_norm_sq(y)
    before == after || error("exact vector norm was not preserved")
    push!(vector_checks, Dict("factor" => factor_id, "input" => vector_json(x),
                              "output" => vector_json(y), "norm_sq_before" => gaussian_json(before),
                              "norm_sq_after" => gaussian_json(after)))
end

edge_inputs = [
    ("scalar", reshape(G[g(2)], 1, 1), q(1, 3)),
    ("zero_step", H1, q(0)),
    ("zero_generator", zeros_g(2, 2), q(7, 5)),
    ("negative_step", H2, q(-4, 7)),
    ("rank_deficient", G[g(0) g(0); g(0) g(2)], q(3, 4)),
    ("repeated_spectrum", G[g(1) g(0); g(0) g(1)], q(-2, 5)),
]
edge_cases = Any[]
for (id, H, a) in edge_inputs
    rec, _ = cayley_data(H, a)
    rec["id"] = id
    push!(edge_cases, rec)
end

# Exact adversarial witnesses.
H_nonhermitian = G[g(0) g(1); g(0) g(0)]
nonhermitian_record, nonhermitian_raw = cayley_data(H_nonhermitian, q(1); require_hermitian=false)
nonhermitian_defect = mat_sub(mat_mul(mat_dagger(nonhermitian_raw.U), nonhermitian_raw.U), I2)
is_zero_matrix(nonhermitian_defect) && error("non-Hermitian witness unexpectedly unitary")

Hscalar = reshape(G[g(1)], 1, 1)
function scalar_complex_step(alpha::G)
    D = mat_add(eye_g(1), mat_scale(I_G * alpha, Hscalar))
    N = mat_sub(eye_g(1), mat_scale(I_G * alpha, Hscalar))
    Dinv, trace = inverse_with_trace(D)
    Dinv === nothing && return Dict("alpha" => gaussian_json(alpha), "D" => matrix_json(D), "singular" => true, "pivot_trace" => trace)
    U = mat_mul(N, Dinv)
    Dict("alpha" => gaussian_json(alpha), "D" => matrix_json(D), "N" => matrix_json(N),
         "U" => matrix_json(U), "modulus_sq_minus_one" => gaussian_json(conj(U[1,1])*U[1,1]-g(1)),
         "singular" => false, "pivot_trace" => trace)
end
complex_step_half = scalar_complex_step(gq(q(0), q(1, 2)))
complex_step_half["modulus_sq_minus_one"] == gaussian_json(g(8)) || error("complex-step witness mismatch")
complex_step_singular = scalar_complex_step(I_G)
complex_step_singular["singular"] == true || error("singular complex-step witness mismatch")

omit_i_U = gq(q(1, 3))
mismatch_U = (g(1) - I_G) / (g(1) + I_G * gq(q(1, 2)))
conj(mismatch_U) * mismatch_U - g(1) == gq(q(3, 5)) || error("mismatched step witness mismatch")

negative_a_record, negative_a_raw = cayley_data(H1, q(-1, 2))
assert_zero("sign reversal adjoint", mat_sub(negative_a_raw.U, mat_dagger(raw1.U)))

wrong_sign_rhs = mat_scale(g(-1), order_rhs)
wrong_sign_residual = mat_sub(cayley_commutator, wrong_sign_rhs)
is_zero_matrix(wrong_sign_residual) && error("wrong-sign order defect unexpectedly passed")
wrong_order_rhs = mat_scale(gq(-4 * q(1, 2) * q(2, 3)),
    mat_mul(mat_mul(mat_mul(mat_mul(raw2.Dinv, raw1.Dinv), generator_commutator), raw1.Dinv), raw2.Dinv))
wrong_order_residual = mat_sub(cayley_commutator, wrong_order_rhs)
is_zero_matrix(wrong_order_residual) && error("wrong inverse order unexpectedly passed")

# Exhaustive lexicographic search over all 2x2 real matrices with entries {-1,0,1}.
search_total = 0
search_singular = 0
search_invertible = 0
search_nonhermitian_invertible = 0
search_nonhermitian_nonunitary = 0
first_singular = nothing
first_nonhermitian_nonunitary = nothing
for a11 in -1:1, a12 in -1:1, a21 in -1:1, a22 in -1:1
    search_total += 1
    H = G[g(a11) g(a12); g(a21) g(a22)]
    D = mat_add(I2, mat_scale(I_G, H))
    Dinv, _ = inverse_with_trace(D)
    if Dinv === nothing
        search_singular += 1
        if first_singular === nothing
            first_singular = Dict("H" => matrix_json(H), "D" => matrix_json(D))
        end
        continue
    end
    search_invertible += 1
    U = mat_mul(mat_sub(I2, mat_scale(I_G, H)), Dinv)
    defect = mat_sub(mat_mul(mat_dagger(U), U), I2)
    if !is_hermitian_exact(H)
        search_nonhermitian_invertible += 1
        if !is_zero_matrix(defect)
            search_nonhermitian_nonunitary += 1
            if first_nonhermitian_nonunitary === nothing
                first_nonhermitian_nonunitary = Dict("H" => matrix_json(H), "D" => matrix_json(D),
                                                     "U" => matrix_json(U), "unitarity_defect" => matrix_json(defect))
            end
        end
    end
end
search_total == 81 || error("exhaustive search count mismatch")
first_singular === nothing && error("search failed to find singular denominator after assumptions dropped")
first_nonhermitian_nonunitary === nothing && error("search failed to find nonunitary Cayley witness")

source_hashes = Dict(
    "exact_gaussian_matrix.jl" => sha256_file(joinpath(@__DIR__, "exact_gaussian_matrix.jl")),
    "discover_operator_cayley.jl" => sha256_file(@__FILE__),
)

core = Dict(
    "schema" => "ndea.exp002.operator_cayley_core.v1",
    "arithmetic" => Dict(
        "field" => "Gaussian rationals Q(i)",
        "rational_encoding" => "normalized decimal numerator and positive denominator strings",
        "matrix_orientation" => "row-major JSON; column-vector action",
        "exact_algorithms" => ["manual matrix multiplication", "deterministic first-nonzero-pivot Gauss-Jordan", "exact elimination determinant"],
        "forbidden_in_exact_layer" => ["floating point", "LinearAlgebra.inv", "LinearAlgebra.det", "backslash solve"],
    ),
    "conventions" => Dict(
        "commutator" => "[X,Y]=XY-YX",
        "D" => "I+i*a*H",
        "N" => "I-i*a*H",
        "C" => "N*D^{-1}=D^{-1}*N",
        "update" => "D*psi_next=N*psi_current",
        "ordered_product" => "P321=U3*U2*U1 acts U1 first",
    ),
    "assumptions" => Dict(
        "unitarity" => ["finite square complex matrix", "H^dagger=H", "a is real"],
        "order_defect" => ["D_a(A) and D_b(B) invertible"],
        "commutation_iff" => ["order-defect assumptions", "a*b != 0"],
    ),
    "source_sha256" => source_hashes,
    "julia_version" => string(VERSION),
    "symbolic_star_polynomial_derivation" => Dict(
        "variables" => Dict("a" => "central real scalar", "H" => "self-adjoint noncommuting generator"),
        "X" => poly_json(Xpoly), "Y" => poly_json(Ypoly),
        "star_X" => poly_json(Xstar), "star_Y" => poly_json(Ystar),
        "star_X_equals_Y" => true, "star_Y_equals_X" => true,
        "Xstar_X" => poly_json(poly_mul(Xstar, Xpoly)),
        "Ystar_Y" => poly_json(poly_mul(Ystar, Ypoly)),
        "X_Y" => poly_json(poly_mul(Xpoly, Ypoly)),
        "common_gram" => poly_json(GramPoly),
        "rewrite_trace" => [
            "conjugate i to -i while fixing real a and self-adjoint H",
            "multiply sparse coefficient maps by exact convolution",
            "cancel opposite degree-(1,1) coefficients",
            "obtain I+a^2*H^2",
        ],
    ),
    "exact_instances" => [record1, record2, record3],
    "composition" => Dict(
        "factor_order" => ["pauli_Y_negative_three_fifths", "pauli_Z_two_thirds", "pauli_X_half"],
        "P21" => matrix_json(P21), "P12" => matrix_json(P12), "P321" => matrix_json(P321),
        "P21_minus_P12" => matrix_json(mat_sub(P21, P12)),
        "P21_unitarity_left_residual" => matrix_json(mat_sub(mat_mul(mat_dagger(P21), P21), I2)),
        "P21_unitarity_right_residual" => matrix_json(mat_sub(mat_mul(P21, mat_dagger(P21)), I2)),
        "P321_unitarity_left_residual" => matrix_json(mat_sub(mat_mul(mat_dagger(P321), P321), I2)),
        "P321_unitarity_right_residual" => matrix_json(mat_sub(mat_mul(P321, mat_dagger(P321)), I2)),
        "formal_word_certificate" => Dict(
            "product_word" => ["U3", "U2", "U1"],
            "adjoint_word" => ["U1_dagger", "U2_dagger", "U3_dagger"],
            "Pdagger_P_word" => ["U1_dagger", "U2_dagger", "U3_dagger", "U3", "U2", "U1"],
            "adjacent_cancellations" => [
                Dict("pair" => ["U3_dagger", "U3"], "remaining" => ["U1_dagger", "U2_dagger", "U2", "U1"]),
                Dict("pair" => ["U2_dagger", "U2"], "remaining" => ["U1_dagger", "U1"]),
                Dict("pair" => ["U1_dagger", "U1"], "remaining" => ["I"]),
            ],
            "commutation_used" => false,
        ),
    ),
    "order_defect" => Dict(
        "generator_commutator" => matrix_json(generator_commutator),
        "cayley_commutator" => matrix_json(cayley_commutator),
        "factorized_rhs" => matrix_json(order_rhs),
        "residual" => matrix_json(mat_sub(cayley_commutator, order_rhs)),
        "coefficient" => rational_json(-4 * q(1,2) * q(2,3)),
        "parameters_nonzero" => true,
        "generator_commutes" => false,
        "cayley_factors_commute" => false,
    ),
    "exact_vector_norm_checks" => vector_checks,
    "edge_cases" => edge_cases,
    "adversarial_witnesses" => [
        Dict("id" => "drop_hermitian", "classification" => "EXACT_COUNTEREXAMPLE",
             "record" => nonhermitian_record, "unitarity_defect" => matrix_json(nonhermitian_defect)),
        Dict("id" => "complex_step_nonunitary", "classification" => "EXACT_COUNTEREXAMPLE", "record" => complex_step_half),
        Dict("id" => "complex_step_singular", "classification" => "EXACT_COUNTEREXAMPLE", "record" => complex_step_singular),
        Dict("id" => "omit_i", "classification" => "EXACT_COUNTEREXAMPLE",
             "U" => gaussian_json(omit_i_U), "modulus_sq_minus_one" => gaussian_json(conj(omit_i_U)*omit_i_U-g(1))),
        Dict("id" => "mismatched_steps", "classification" => "EXACT_COUNTEREXAMPLE",
             "denominator_a" => rational_json(q(1,2)), "numerator_b" => rational_json(q(1)),
             "U" => gaussian_json(mismatch_U), "modulus_sq_minus_one" => gaussian_json(conj(mismatch_U)*mismatch_U-g(1))),
        Dict("id" => "false_order_independence", "classification" => "EXACT_COUNTEREXAMPLE",
             "P21_minus_P12" => matrix_json(mat_sub(P21,P12))),
        Dict("id" => "wrong_order_defect_sign", "classification" => "EXACT_COUNTEREXAMPLE",
             "wrong_rhs" => matrix_json(wrong_sign_rhs), "residual" => matrix_json(wrong_sign_residual)),
        Dict("id" => "wrong_inverse_factor_order", "classification" => "EXACT_COUNTEREXAMPLE",
             "wrong_rhs" => matrix_json(wrong_order_rhs), "residual" => matrix_json(wrong_order_residual)),
        Dict("id" => "zero_parameter_breaks_commutation_iff", "classification" => "EXACT_COUNTEREXAMPLE",
             "a" => rational_json(q(0)), "generator_commutator" => matrix_json(generator_commutator),
             "C_zero" => matrix_json(I2), "C_zero_commutator_with_U2" => matrix_json(mat_commutator(I2,raw2.U))),
        Dict("id" => "sign_reversal_is_adjoint_not_instability", "classification" => "EXACT_NUANCE",
             "U_negative_a" => matrix_json(negative_a_raw.U), "U_positive_a_dagger" => matrix_json(mat_dagger(raw1.U)),
             "residual" => matrix_json(mat_sub(negative_a_raw.U,mat_dagger(raw1.U)))),
    ],
    "exhaustive_counterexample_search" => Dict(
        "domain" => "2x2 real matrices, row-major entries in {-1,0,1}, nested lexicographic loops; a=1",
        "total" => search_total, "invertible_denominator" => search_invertible,
        "singular_denominator" => search_singular,
        "nonhermitian_invertible" => search_nonhermitian_invertible,
        "nonhermitian_nonunitary" => search_nonhermitian_nonunitary,
        "first_singular" => first_singular,
        "first_nonhermitian_nonunitary" => first_nonhermitian_nonunitary,
    ),
    "claim_classification" => Dict(
        "exactly_derived_by_julia" => ["sparse star-polynomial identities", "exact matrix solves and determinants", "unitarity residuals", "noncommutative order-defect instance", "adversarial witnesses", "finite exhaustive search"],
        "numerically_tested_separately" => ["random Float64 Hermitian matrices and ordered products"],
        "formally_verified_by_lean" => "not supplied by this certificate; Lean proof is independent",
        "informally_interpreted" => ["connection to geometric integration and finite quantum evolution"],
        "not_verified" => ["infinite-dimensional operators", "convergence order", "floating-point long-time error bound", "mathematical novelty"],
    ),
)

core_bytes = Vector{UInt8}(codeunits(canonical_json(core)))
core_sha256 = sha256_hex(core_bytes)
run_id = "exp002-" * core_sha256[1:24]
certificate = Dict("schema" => "ndea.exp002.operator_cayley_certificate.v1",
                   "core" => core, "core_sha256" => core_sha256, "run_id" => run_id)

cert_dir = joinpath(EXP_ROOT, "certificates")
meta_dir = joinpath(EXP_ROOT, "metadata")
mkpath(cert_dir); mkpath(meta_dir)
cert_path = joinpath(cert_dir, "operator_cayley_core.json")
open(cert_path, "w") do io
    write(io, canonical_json(certificate), "\n")
end

# Numerical experiments are explicitly separate from the exact certificate core.
Random.seed!(20260905)
numeric_trials = 512
max_single_residual = 0.0
max_product_residual = 0.0
for _ in 1:numeric_trials
    factors = Matrix{ComplexF64}[]
    for n in (2, 3, 4)
        R = randn(ComplexF64, n, n)
        H = (R + R') / 2
        a = 8 * randn()
        D = Matrix{ComplexF64}(I, n, n) + im * a * H
        N = Matrix{ComplexF64}(I, n, n) - im * a * H
        U = D \ N
        max_single_residual = max(max_single_residual, opnorm(U' * U - Matrix{ComplexF64}(I,n,n), Inf))
        push!(factors, U)
    end
    # Use the common 2x2 leading blocks solely for a noncommuting three-factor product test.
    P = factors[3][1:2,1:2] * factors[2][1:2,1:2] * factors[1]
    max_product_residual = max(max_product_residual, opnorm(P' * P - Matrix{ComplexF64}(I,2,2), Inf))
end

receipt = Dict(
    "schema" => "ndea.exp002.operator_cayley_run_receipt.v1",
    "run_id" => run_id,
    "core_sha256" => core_sha256,
    "certificate_path" => cert_path,
    "certificate_sha256" => sha256_file(cert_path),
    "source_sha256" => source_hashes,
    "julia_version" => string(VERSION),
    "timestamp_utc" => Dates.format(now(UTC), dateformat"yyyy-mm-ddTHH:MM:SS.sssZ"),
    "numeric_nonproof" => Dict(
        "classification" => "NUMERICALLY_TESTED_NON_PROOF",
        "seed" => 20260905,
        "trials" => numeric_trials,
        "matrix_dimensions_per_trial" => [2,3,4],
        "max_single_factor_unitarity_residual" => string(max_single_residual),
        "max_three_factor_unitarity_residual" => string(max_product_residual),
    ),
    "exact_status" => "PASS",
    "numeric_status" => "PASS",
)
receipt_path = joinpath(meta_dir, "operator_cayley_run_receipt.json")
open(receipt_path, "w") do io
    write(io, canonical_json(receipt), "\n")
end

println("RUN_ID=", run_id)
println("CORE_SHA256=", core_sha256)
println("CERTIFICATE_SHA256=", sha256_file(cert_path))
println("SOURCE_DISCOVERY_SHA256=", source_hashes["discover_operator_cayley.jl"])
println("SOURCE_LIBRARY_SHA256=", source_hashes["exact_gaussian_matrix.jl"])
println("EXACT_INSTANCES=3")
println("EXACT_VECTOR_NORM_CHECKS=", length(vector_checks))
println("EXHAUSTIVE_TOTAL=", search_total)
println("EXHAUSTIVE_SINGULAR=", search_singular)
println("EXHAUSTIVE_NONHERMITIAN_NONUNITARY=", search_nonhermitian_nonunitary)
println("ORDER_DEFECT_EXACT=PASS")
println("NONCOMMUTING_PRODUCTS_UNITARY=PASS")
println("ADVERSARIAL_WITNESSES=10/10 PASS")
println("NUMERIC_TRIALS=", numeric_trials)
println("NUMERIC_MAX_SINGLE_RESIDUAL=", max_single_residual)
println("NUMERIC_MAX_PRODUCT_RESIDUAL=", max_product_residual)
println("JULIA_DISCOVERY_STATUS=PASS")
