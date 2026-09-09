using Dates
using Random
using SHA

const Q = Rational{BigInt}
const CQ = Complex{Q}
const RNG_SEED = 0x4e444541

q(n::Integer, d::Integer=1) = BigInt(n) // BigInt(d)
cq(r::Integer=0, i::Integer=0) = CQ(q(r), q(i))

function trim_poly(p)
    result = copy(p)
    while length(result) > 1 && iszero(result[end])
        pop!(result)
    end
    result
end

function poly_add(a::Vector{T}, b::Vector{T}) where T
    result = fill(zero(T), max(length(a), length(b)))
    for index in eachindex(a)
        result[index] += a[index]
    end
    for index in eachindex(b)
        result[index] += b[index]
    end
    trim_poly(result)
end

function poly_scale(c::T, a::Vector{T}) where T
    trim_poly(T[c * value for value in a])
end

function poly_mul(a::Vector{T}, b::Vector{T}) where T
    result = fill(zero(T), length(a) + length(b) - 1)
    for ia in eachindex(a), ib in eachindex(b)
        result[ia + ib - 1] += a[ia] * b[ib]
    end
    trim_poly(result)
end

function laurent_add_term!(p::Dict{Int,Q}, exponent::Int, coefficient::Q)
    p[exponent] = get(p, exponent, q(0)) + coefficient
    iszero(p[exponent]) && delete!(p, exponent)
    p
end

function laurent_mul(a::Dict{Int,Q}, b::Dict{Int,Q})
    result = Dict{Int,Q}()
    for (ea, ca) in a, (eb, cb) in b
        laurent_add_term!(result, ea + eb, ca * cb)
    end
    result
end

function laurent_eval(p::Dict{Int,Q}, z::Q)
    iszero(z) && any(exponent < 0 for exponent in keys(p)) &&
        throw(DomainError(z, "cannot evaluate negative Laurent powers at zero"))
    result = q(0)
    for (exponent, coefficient) in p
        result += coefficient * z^exponent
    end
    result
end

rat_json(x::Q) = Dict(
    "numerator" => string(numerator(x)),
    "denominator" => string(denominator(x)),
)

complex_rat_json(x::CQ) = Dict(
    "real" => rat_json(real(x)),
    "imaginary" => rat_json(imag(x)),
)

poly_q_json(p::Vector{Q}) = [
    Dict("degree" => index - 1, "coefficient" => rat_json(coefficient))
    for (index, coefficient) in enumerate(p)
]

poly_cq_json(p::Vector{CQ}) = [
    Dict("degree" => index - 1, "coefficient" => complex_rat_json(coefficient))
    for (index, coefficient) in enumerate(p)
]

laurent_json(p::Dict{Int,Q}) = [
    Dict("exponent" => exponent, "coefficient" => rat_json(p[exponent]))
    for exponent in sort(collect(keys(p)))
]

function json_escape(value::AbstractString)
    replace(
        String(value),
        "\\" => "\\\\",
        "\"" => "\\\"",
        "\b" => "\\b",
        "\f" => "\\f",
        "\n" => "\\n",
        "\r" => "\\r",
        "\t" => "\\t",
    )
end

function to_json(value, indent::Int=0)
    pad = repeat(" ", indent)
    nextpad = repeat(" ", indent + 2)
    if value === nothing
        return "null"
    elseif value isa Bool
        return value ? "true" : "false"
    elseif value isa Integer
        return string(value)
    elseif value isa AbstractFloat
        isfinite(value) || error("non-finite floating-point value is not valid JSON")
        return repr(value)
    elseif value isa AbstractString
        return "\"" * json_escape(value) * "\""
    elseif value isa AbstractDict
        keys_sorted = sort(collect(keys(value)); by=string)
        isempty(keys_sorted) && return "{}"
        entries = String[]
        for key in keys_sorted
            push!(entries, nextpad * to_json(string(key)) * ": " * to_json(value[key], indent + 2))
        end
        return "{\n" * join(entries, ",\n") * "\n" * pad * "}"
    elseif value isa AbstractVector || value isa Tuple
        isempty(value) && return "[]"
        entries = [nextpad * to_json(item, indent + 2) for item in value]
        return "[\n" * join(entries, ",\n") * "\n" * pad * "]"
    else
        error("unsupported JSON value type: $(typeof(value))")
    end
end

println("NDEA-Evolve Experiment 001 — Julia discovery")
println("Julia VERSION=$(VERSION)")
println("RNG seed=$(Int(RNG_SEED))")

# Construct the centered negative-Laplacian symbol from the stencil itself.
stencil_terms = [(0, q(2)), (-1, q(-1)), (1, q(-1))]
stencil_symbol = Dict{Int,Q}()
for (shift, weight) in stencil_terms
    laurent_add_term!(stencil_symbol, shift, weight)
end

one_minus_z = Dict(0 => q(1), 1 => q(-1))
one_minus_zinv = Dict(0 => q(1), -1 => q(-1))
factorized_symbol = laurent_mul(one_minus_z, one_minus_zinv)
@assert stencil_symbol == factorized_symbol

# Exact half-angle rewrite: with s = sin(theta/2), cos(theta) = 1 - 2s^2.
# Coefficient vectors are in ascending powers of s.
two_poly = Q[q(2)]
cos_theta_as_s = Q[q(1), q(0), q(-2)]
minus_two_cos_theta_as_s = poly_scale(q(-2), cos_theta_as_s)
symbol_as_s = poly_add(two_poly, minus_two_cos_theta_as_s)
expected_symbol_as_s = Q[q(0), q(0), q(4)]
@assert symbol_as_s == expected_symbol_as_s

# Exact Gaussian-rational polynomial certificate for Cayley unit modulus.
# Coefficient vectors are in ascending powers of the real scalar a=k*lambda/2.
pminus = CQ[cq(1, 0), cq(0, -1)]
pplus = CQ[cq(1, 0), cq(0, 1)]
numerator_norm_squared = poly_mul(pminus, conj.(pminus))
denominator_norm_squared = poly_mul(pplus, conj.(pplus))
common_norm_squared = CQ[cq(1, 0), cq(0, 0), cq(1, 0)]
@assert numerator_norm_squared == common_norm_squared
@assert denominator_norm_squared == common_norm_squared

# Structured exact certificate that solving
#   pplus(a) * c_next = pminus(a) * c_current
# by G(a)=c_next/c_current=pminus(a)/pplus(a) satisfies the scalar equation
# after cross multiplication.
cayley_cross_multiplication_left = poly_mul(pplus, pminus)
cayley_cross_multiplication_right = poly_mul(pminus, pplus)
@assert cayley_cross_multiplication_left == cayley_cross_multiplication_right

exact_cayley_samples = Any[]
for a in Q[q(-3, 2), q(0), q(5, 7), q(11, 3)]
    numerator = complex(q(1), -a)
    denominator = complex(q(1), a)
    @assert !iszero(denominator)
    amplification = numerator / denominator
    @assert denominator * amplification == numerator
    @assert abs2(amplification) == q(1)
    push!(exact_cayley_samples, Dict(
        "a" => rat_json(a),
        "amplification_real" => rat_json(real(amplification)),
        "amplification_imaginary" => rat_json(imag(amplification)),
        "abs_squared" => rat_json(abs2(amplification)),
        "status" => "EXACT_RATIONAL_IDENTITY",
    ))
end

function periodic_mode(N::Int, m::Int, j::Int)
    N > 0 || throw(DomainError(N, "N must be positive"))
    theta = (BigFloat(2) * BigFloat(pi) * BigFloat(m)) / BigFloat(N)
    cis(theta * BigFloat(mod(j, N)))
end

function derived_lambda(theta, h)
    iszero(h) && throw(DomainError(h, "h must be nonzero"))
    (BigFloat(4) / (h * h)) * sin(theta / BigFloat(2))^2
end

edge_results = Any[]
bigfloat_summary = setprecision(BigFloat, 256) do
    max_periodicity_error = BigFloat(0)
    max_eigen_error = BigFloat(0)
    max_modulus_error = BigFloat(0)
    case_count = 0
    for N in (1, 2, 3, 4, 8, 17), m in 0:(N - 1), j in (-N - 1, -1, 0, N - 1, N, N + 1)
        theta = (BigFloat(2) * BigFloat(pi) * BigFloat(m)) / BigFloat(N)
        phi_j = periodic_mode(N, m, j)
        periodicity_error = abs(periodic_mode(N, m, j + N) - phi_j)
        max_periodicity_error = max(max_periodicity_error, periodicity_error)
        for h_text in ("0.03125", "0.5", "1.0", "-2.0", "16.0"), k_text in ("-3.0", "0.0", "0.125", "5.0")
            h = parse(BigFloat, h_text)
            k = parse(BigFloat, k_text)
            laplacian_action = (
                BigFloat(2) * phi_j - periodic_mode(N, m, j - 1) - periodic_mode(N, m, j + 1)
            ) / (h * h)
            lambda = derived_lambda(theta, h)
            eigen_error = abs(laplacian_action - lambda * phi_j)
            a = (k / BigFloat(2)) * lambda
            amplification = (one(Complex{BigFloat}) - im * a) / (one(Complex{BigFloat}) + im * a)
            modulus_error = abs(abs2(amplification) - BigFloat(1))
            max_eigen_error = max(max_eigen_error, eigen_error)
            max_modulus_error = max(max_modulus_error, modulus_error)
            case_count += 1
        end
    end
    tolerance = parse(BigFloat, "1e-60")
    @assert max_periodicity_error < tolerance
    @assert max_eigen_error < tolerance
    @assert max_modulus_error < tolerance
    Dict(
        "precision_bits" => precision(BigFloat),
        "case_count" => case_count,
        "tolerance" => string(tolerance),
        "max_periodicity_error" => string(max_periodicity_error),
        "max_eigen_residual" => string(max_eigen_error),
        "max_modulus_squared_error" => string(max_modulus_error),
        "status" => "PASS_FLOATING_POINT_EXPERIMENT",
    )
end

push!(edge_results, Dict(
    "case" => "constant mode theta=0",
    "expected_lambda" => "0",
    "expected_amplification" => "1 when lambda=0",
    "status" => "STANDARD_ANALYTIC_SPECIAL_VALUE",
))
push!(edge_results, Dict(
    "case" => "Nyquist mode theta=pi",
    "expected_lambda" => "4/h^2",
    "status" => "STANDARD_ANALYTIC_SPECIAL_VALUE",
))
push!(edge_results, Dict(
    "case" => "k=0",
    "expected_amplification" => "1",
    "status" => "STANDARD_ANALYTIC_SPECIAL_VALUE",
))
push!(edge_results, Dict(
    "case" => "h=0",
    "expected" => "DomainError; excluded by h != 0 / physical h > 0",
    "status" => "GUARD_REJECTED",
))
try
    derived_lambda(BigFloat(1), BigFloat(0))
    error("h=0 guard unexpectedly accepted")
catch err
    @assert err isa DomainError
end

function run_random_search(seed, random_case_count)
    rng = MersenneTwister(seed)
    absolute_tolerance = 2e-9
    relative_tolerance = 5e-13
    max_random_eigen_error = 0.0
    max_random_normalized_eigen_error = 0.0
    max_mixed_bound_ratio = 0.0
    max_random_modulus_error = 0.0
    max_random_periodicity_error = 0.0
    for _ in 1:random_case_count
        N = rand(rng, 1:96)
        m = rand(rng, -2N:2N)
        j = rand(rng, -3N:3N)
        h_magnitude = 10.0^(6.0 * rand(rng) - 3.0)
        h = rand(rng, Bool) ? h_magnitude : -h_magnitude
        k = 20.0 * rand(rng) - 10.0
        theta = 2pi * m / N
        phi(index) = cis(theta * mod(index, N))
        laplacian_action = (2phi(j) - phi(j - 1) - phi(j + 1)) / h^2
        lambda = (4 / h^2) * sin(theta / 2)^2
        a = (k / 2) * lambda
        amplification = (1 - im * a) / (1 + im * a)
        expected = lambda * phi(j)
        eigen_error = abs(laplacian_action - expected)
        scale = max(1.0, abs(laplacian_action), abs(expected))
        mixed_bound = absolute_tolerance + relative_tolerance * scale
        max_random_eigen_error = max(max_random_eigen_error, eigen_error)
        max_random_normalized_eigen_error = max(max_random_normalized_eigen_error, eigen_error / scale)
        max_mixed_bound_ratio = max(max_mixed_bound_ratio, eigen_error / mixed_bound)
        max_random_modulus_error = max(max_random_modulus_error, abs(abs2(amplification) - 1))
        max_random_periodicity_error = max(max_random_periodicity_error, abs(phi(j + N) - phi(j)))
    end
    @assert max_mixed_bound_ratio <= 1.0
    @assert max_random_modulus_error < 5e-13
    @assert max_random_periodicity_error < 5e-13
    Dict(
        "rng" => "Random.MersenneTwister",
        "seed" => Int(seed),
        "case_count" => random_case_count,
        # Decimal strings make cross-language canonical-core hashing exact.
        "eigen_absolute_tolerance" => string(absolute_tolerance),
        "eigen_relative_tolerance" => string(relative_tolerance),
        "max_eigen_residual" => string(max_random_eigen_error),
        "max_normalized_eigen_residual" => string(max_random_normalized_eigen_error),
        "max_mixed_bound_ratio" => string(max_mixed_bound_ratio),
        "max_modulus_squared_error" => string(max_random_modulus_error),
        "max_periodicity_error" => string(max_random_periodicity_error),
        "status" => "PASS_FLOAT64_COUNTEREXAMPLE_SEARCH",
    )
end

random_summary = run_random_search(RNG_SEED, 256)

# Adversarial/counterexample witnesses.
# The wrong full-angle expression 4*sin(theta)^2 has Laurent symbol
# 2-z^2-z^(-2).  At the exact rational unit-circle point z=-1 (theta=pi),
# it is zero, whereas the derived centered-stencil symbol is four.
wrong_full_angle_symbol = Dict(-2 => q(-1), 0 => q(2), 2 => q(-1))
wrong_eigen_witness_z = q(-1)
wrong_eigen_correct = laurent_eval(stencil_symbol, wrong_eigen_witness_z)
wrong_eigen_candidate = laurent_eval(wrong_full_angle_symbol, wrong_eigen_witness_z)
@assert wrong_eigen_correct == q(4)
@assert wrong_eigen_candidate == q(0)
@assert wrong_eigen_correct != wrong_eigen_candidate

reversed_stencil = Dict(exponent => -coefficient for (exponent, coefficient) in stencil_symbol)
@assert reversed_stencil != stencil_symbol

a_one = q(1)
wrong_numerator = CQ[cq(1, 0), cq(-1, 0)]
wrong_numerator_norm_squared = poly_mul(wrong_numerator, conj.(wrong_numerator))
@assert wrong_numerator_norm_squared == CQ[cq(1), cq(-2), cq(1)]
@assert wrong_numerator_norm_squared != common_norm_squared
wrong_amplification_at_one = complex(q(1) - a_one, q(0)) / complex(q(1), a_one)
@assert abs2(wrong_amplification_at_one) == q(0)

nonreal_a = CQ(q(0), q(1, 2))
exact_i = cq(0, 1)
nonreal_amplification = (cq(1) - exact_i * nonreal_a) / (cq(1) + exact_i * nonreal_a)
@assert nonreal_amplification == cq(3)
@assert abs2(nonreal_amplification) == q(9)

adversarial_checks = [
    Dict(
        "id" => "ADV_WRONG_EIGENVALUE_ARGUMENT",
        "conjecture" => "lambda_wrong=4*sin(theta)^2/h^2",
        "correct_symbol" => laurent_json(stencil_symbol),
        "altered_symbol" => laurent_json(wrong_full_angle_symbol),
        "witness" => Dict(
            "theta" => "pi",
            "h" => rat_json(q(1)),
            "z" => rat_json(wrong_eigen_witness_z),
            "correct_value" => rat_json(wrong_eigen_correct),
            "wrong_value" => rat_json(wrong_eigen_candidate),
        ),
        "counterexample_found" => true,
        "status" => "EXACT_LAURENT_EVALUATION_COUNTEREXAMPLE",
    ),
    Dict(
        "id" => "ADV_REVERSED_STENCIL_SIGN",
        "conjecture" => "negative stencil coefficients equal centered negative-Laplacian coefficients",
        "derived" => laurent_json(stencil_symbol),
        "altered" => laurent_json(reversed_stencil),
        "counterexample_found" => true,
        "status" => "EXACT_COEFFICIENT_MISMATCH",
    ),
    Dict(
        "id" => "ADV_WRONG_CAYLEY_NUMERATOR",
        "conjecture" => "(1-a)/(1+i*a) has unit modulus for every real a",
        "wrong_numerator_polynomial" => poly_cq_json(wrong_numerator),
        "wrong_numerator_norm_polynomial" => poly_cq_json(wrong_numerator_norm_squared),
        "correct_denominator_norm_polynomial" => poly_cq_json(denominator_norm_squared),
        "witness" => Dict(
            "a" => rat_json(a_one),
            "modulus_squared" => rat_json(abs2(wrong_amplification_at_one)),
        ),
        "counterexample_found" => true,
        "status" => "EXACT_RATIONAL_COUNTEREXAMPLE",
    ),
    Dict(
        "id" => "ADV_DROP_REAL_PARAMETER",
        "conjecture" => "Cayley factor has unit modulus for arbitrary complex a",
        "witness" => Dict(
            "a" => complex_rat_json(nonreal_a),
            "amplification" => complex_rat_json(nonreal_amplification),
            "modulus_squared" => rat_json(abs2(nonreal_amplification)),
        ),
        "counterexample_found" => true,
        "status" => "EXACT_GAUSSIAN_RATIONAL_COUNTEREXAMPLE",
    ),
    Dict(
        "id" => "ADV_ZERO_GRID_SPACING",
        "conjecture" => "the eigenvalue formula is defined for h=0",
        "witness" => Dict("h" => rat_json(q(0)), "result" => "DomainError"),
        "counterexample_found" => true,
        "status" => "DOMAIN_GUARD_REJECTION",
    ),
]

source_sha256 = bytes2hex(sha256(read(@__FILE__)))
core = Dict(
    "schema_version" => "ndea-evolve.exp001.fourier-stability.v1",
    "experiment" => Dict(
        "id" => "NDEA-Evolve Experiment 001",
        "mission" => "Julia discovery and Lean verification of periodic Fourier-mode Cayley-Crank-Nicolson stability",
    ),
    "assumptions" => [
        Dict("id" => "A1", "statement" => "N is a positive integer"),
        Dict("id" => "A2", "statement" => "m is an integer and theta=2*pi*m/N"),
        Dict("id" => "A3", "statement" => "h is real and nonzero; the physical grid-spacing theorem assumes h>0"),
        Dict("id" => "A4", "statement" => "k is real"),
        Dict("id" => "A5", "statement" => "z=exp(i*theta), hence z^N=1 and z^(-1)=conj(z)"),
    ],
    "operator_derivation" => Dict(
        "mode" => "phi_j=z^j with z=exp(i*theta)",
        "periodic_quantization" => "theta=2*pi*m/N",
        "operator" => "(-Delta_h u)_j=(2*u_j-u_(j-1)-u_(j+1))/h^2",
        "constructed_stencil_terms" => [
            Dict("shift" => shift, "weight" => rat_json(weight)) for (shift, weight) in stencil_terms
        ],
        "constructed_laurent_symbol" => laurent_json(stencil_symbol),
        "factor_left" => laurent_json(one_minus_z),
        "factor_right" => laurent_json(one_minus_zinv),
        "factorization_product" => laurent_json(factorized_symbol),
        "factorization_exact" => true,
        "half_angle_coefficient_certificate" => Dict(
            "variable" => "s=sin(theta/2)",
            "constant_two_polynomial" => poly_q_json(two_poly),
            "cos_theta_as_s_polynomial" => poly_q_json(cos_theta_as_s),
            "minus_two_cos_theta_polynomial" => poly_q_json(minus_two_cos_theta_as_s),
            "derived_symbol_polynomial" => poly_q_json(symbol_as_s),
            "expected_symbol_polynomial" => poly_q_json(expected_symbol_as_s),
            "operation" => "2+(-2)*(1-2*s^2)",
            "exact_coefficient_equality" => true,
        ),
        "simplification_steps" => [
            Dict(
                "from" => "(2*phi_j-phi_(j-1)-phi_(j+1))/(h^2*phi_j)",
                "rule" => "phi_(j+1)=z*phi_j and phi_(j-1)=z^(-1)*phi_j",
                "to" => "(2-z^(-1)-z)/h^2",
                "status" => "EXACT_LAURENT_IDENTITY",
            ),
            Dict(
                "from" => "2-z^(-1)-z",
                "rule" => "z=exp(i*theta), z+z^(-1)=2*cos(theta)",
                "to" => "2-2*cos(theta)",
                "status" => "STANDARD_ANALYTIC_IDENTITY",
            ),
            Dict(
                "from" => "2-2*cos(theta)",
                "rule" => "cos(theta)=1-2*sin(theta/2)^2",
                "to" => "4*sin(theta/2)^2",
                "coefficient_certificate" => poly_q_json(symbol_as_s),
                "status" => "EXACT_COEFFICIENT_IDENTITY_PLUS_STANDARD_TRIG_IDENTITY",
            ),
        ],
        "derived_eigenvalue" => "lambda_h(theta)=4*sin(theta/2)^2/h^2",
        "nonnegative_for_real_theta_nonzero_h" => true,
    ),
    "cayley_crank_nicolson_derivation" => Dict(
        "scalar_update_equation" => "(1+i*(k/2)*lambda)*c_next=(1-i*(k/2)*lambda)*c_current",
        "substitution" => "a=(k/2)*lambda",
        "solved_ratio" => "G=c_next/c_current=(1-i*a)/(1+i*a)",
        "derived_amplification_factor" => "G(theta)=(1-i*(k/2)*lambda_h(theta))/(1+i*(k/2)*lambda_h(theta))",
        "denominator_nonzero_reason" => "for real a, |1+i*a|^2=1+a^2>=1",
        "structured_scalar_equation" => Dict(
            "left_factor_times_c_next" => poly_cq_json(pplus),
            "right_factor_times_c_current" => poly_cq_json(pminus),
        ),
        "structured_solution" => Dict(
            "amplification_numerator" => poly_cq_json(pminus),
            "amplification_denominator" => poly_cq_json(pplus),
            "cross_multiplication_left" => poly_cq_json(cayley_cross_multiplication_left),
            "cross_multiplication_right" => poly_cq_json(cayley_cross_multiplication_right),
            "exact_coefficient_equality" => true,
        ),
    ),
    "unit_modulus_certificate" => Dict(
        "coefficient_domain" => "Complex{Rational{BigInt}}[a]",
        "numerator_polynomial" => poly_cq_json(pminus),
        "denominator_polynomial" => poly_cq_json(pplus),
        "numerator_times_conjugate" => poly_cq_json(numerator_norm_squared),
        "denominator_times_conjugate" => poly_cq_json(denominator_norm_squared),
        "common_norm_squared" => "1+a^2",
        "exact_coefficient_equalities" => true,
        "exact_rational_samples" => exact_cayley_samples,
    ),
    "checks" => Dict(
        "edge_cases" => edge_results,
        "high_precision_periodic_modes" => bigfloat_summary,
        "fixed_seed_random_search" => random_summary,
        "adversarial_counterexamples" => adversarial_checks,
    ),
    "exact_vs_numerical" => Dict(
        "exact" => [
            "stencil Laurent coefficients",
            "Laurent factorization",
            "half-angle coefficient substitution after the standard trig identity",
            "Cayley numerator/denominator coefficient derivation",
            "Cayley scalar-equation cross-multiplication certificate",
            "Gaussian-rational norm-squared polynomial equality",
            "rational Cayley samples",
            "Laurent-polynomial adversarial eigenvalue witness",
            "Gaussian-rational and rational adversarial witnesses",
        ],
        "numerical" => [
            "periodic-mode boundary checks with 256-bit BigFloat",
            "eigenvector residual checks with 256-bit BigFloat",
            "unit-modulus residual checks with 256-bit BigFloat",
            "256 fixed-seed Float64 counterexample-search cases",
        ],
        "analytic_not_proved_by_julia" => [
            "Euler formula and z+z^(-1)=2*cos(theta)",
            "cos(theta)=1-2*sin(theta/2)^2",
            "the declarative constant-mode, Nyquist-mode, and k=0 special-value interpretations",
        ],
    ),
    "trust_boundary" => Dict(
        "julia_boolean_trusted_by_lean" => false,
        "certificate_parsed_by_lean" => false,
        "lean_rederives_general_theorems" => true,
        "certificate_role" => "auditable discovery and computation artifact, not a proof oracle",
    ),
    "source_sha256" => source_sha256,
    "canonicalization" => "UTF-8 JSON with lexicographically sorted object keys, two-space indentation, and one trailing LF; nonintegral numeric observations are decimal strings",
    "overall_status" => "PASS",
)

canonical_core = to_json(core) * "\n"
core_sha256 = bytes2hex(sha256(codeunits(canonical_core)))
timestamp_utc = get(ENV, "NDEA_RUN_TIMESTAMP_UTC", string(now(UTC)) * "Z")
run_id = "exp001-" * core_sha256[1:12] * "-" * replace(timestamp_utc, r"[^0-9]" => "")[1:14]

certificate = copy(core)
certificate["run"] = Dict(
    "run_id" => run_id,
    "timestamp_utc" => timestamp_utc,
    "julia_version" => string(VERSION),
    "julia_executable" => joinpath(Sys.BINDIR, Base.julia_exename()),
    "rng_algorithm" => "Random.MersenneTwister",
    "rng_seed" => Int(RNG_SEED),
    "core_certificate_sha256" => core_sha256,
)

certificate_path = length(ARGS) >= 1 ? abspath(ARGS[1]) : abspath(joinpath(@__DIR__, "..", "..", "certificates", "fourier_certificate.json"))
mkpath(dirname(certificate_path))
open(certificate_path, "w") do io
    write(io, to_json(certificate))
    write(io, "\n")
end
certificate_sha256 = bytes2hex(sha256(read(certificate_path)))

println("EXACT_STENCIL_SYMBOL=$(sort(collect(stencil_symbol)))")
println("EXACT_LAURENT_FACTORIZATION=PASS")
println("EXACT_HALF_ANGLE_COEFFICIENT_CERTIFICATE=PASS")
println("EXACT_CAYLEY_SCALAR_CROSS_MULTIPLICATION=PASS")
println("EXACT_CAYLEY_NORM_POLYNOMIAL_CERTIFICATE=PASS")
println("EXACT_WRONG_EIGENVALUE_LAURENT_WITNESS=PASS")
println("EXACT_NONREAL_PARAMETER_GAUSSIAN_RATIONAL_WITNESS=PASS")
println("HIGH_PRECISION_CASES=", bigfloat_summary["case_count"])
println("HIGH_PRECISION_MAX_EIGEN_RESIDUAL=", bigfloat_summary["max_eigen_residual"])
println("HIGH_PRECISION_MAX_MODULUS_SQUARED_ERROR=", bigfloat_summary["max_modulus_squared_error"])
println("RANDOM_COUNTEREXAMPLE_SEARCH_CASES=", random_summary["case_count"])
println("RANDOM_MAX_EIGEN_RESIDUAL=", random_summary["max_eigen_residual"])
println("RANDOM_MAX_NORMALIZED_EIGEN_RESIDUAL=", random_summary["max_normalized_eigen_residual"])
println("RANDOM_MAX_MIXED_BOUND_RATIO=", random_summary["max_mixed_bound_ratio"])
println("RANDOM_MAX_MODULUS_SQUARED_ERROR=", random_summary["max_modulus_squared_error"])
println("ADVERSARIAL_COUNTEREXAMPLES_FOUND=", count(item -> item["counterexample_found"], adversarial_checks), "/", length(adversarial_checks))
println("CERTIFICATE_PATH=$(certificate_path)")
println("CERTIFICATE_SHA256=$(certificate_sha256)")
println("RUN_ID=$(run_id)")
println("JULIA_DISCOVERY_STATUS=PASS")
