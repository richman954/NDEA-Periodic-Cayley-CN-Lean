module ExactGaussianMatrix

using SHA

const Q = Rational{BigInt}
const G = Complex{Q}

q(n::Integer, d::Integer=1) = Q(BigInt(n), BigInt(d))
g(re::Integer, im::Integer=0) = G(q(re), q(im))
gq(re::Q, im::Q=q(0)) = G(re, im)

function eye_g(n::Int)
    M = fill(g(0), n, n)
    for i in 1:n
        M[i, i] = g(1)
    end
    M
end

zeros_g(rows::Int, cols::Int) = fill(g(0), rows, cols)

function mat_add(A::Matrix{G}, B::Matrix{G})
    size(A) == size(B) || error("matrix dimension mismatch in add")
    C = similar(A)
    for i in axes(A, 1), j in axes(A, 2)
        C[i, j] = A[i, j] + B[i, j]
    end
    C
end

function mat_sub(A::Matrix{G}, B::Matrix{G})
    size(A) == size(B) || error("matrix dimension mismatch in subtract")
    C = similar(A)
    for i in axes(A, 1), j in axes(A, 2)
        C[i, j] = A[i, j] - B[i, j]
    end
    C
end

function mat_scale(c::G, A::Matrix{G})
    C = similar(A)
    for i in axes(A, 1), j in axes(A, 2)
        C[i, j] = c * A[i, j]
    end
    C
end

function mat_mul(A::Matrix{G}, B::Matrix{G})
    size(A, 2) == size(B, 1) || error("matrix dimension mismatch in multiply")
    C = zeros_g(size(A, 1), size(B, 2))
    for i in axes(A, 1), j in axes(B, 2)
        total = g(0)
        for k in axes(A, 2)
            total += A[i, k] * B[k, j]
        end
        C[i, j] = total
    end
    C
end

function mat_dagger(A::Matrix{G})
    C = zeros_g(size(A, 2), size(A, 1))
    for i in axes(A, 1), j in axes(A, 2)
        C[j, i] = conj(A[i, j])
    end
    C
end

mat_commutator(A::Matrix{G}, B::Matrix{G}) = mat_sub(mat_mul(A, B), mat_mul(B, A))
is_zero_matrix(A::Matrix{G}) = all(iszero, A)
is_hermitian_exact(A::Matrix{G}) = size(A, 1) == size(A, 2) && A == mat_dagger(A)

function determinant_exact(A::Matrix{G})
    n, m = size(A)
    n == m || error("determinant requires square matrix")
    M = copy(A)
    det_value = g(1)
    swaps = 0
    pivots = Any[]
    for col in 1:n
        pivot_row = findfirst(row -> !iszero(M[row, col]), col:n)
        if pivot_row === nothing
            push!(pivots, Dict("column" => col, "status" => "ZERO_COLUMN"))
            return g(0), Dict("row_swaps" => swaps, "pivots" => pivots, "singular" => true)
        end
        pivot_row = col - 1 + pivot_row
        if pivot_row != col
            M[col, :], M[pivot_row, :] = copy(M[pivot_row, :]), copy(M[col, :])
            swaps += 1
        end
        pivot = M[col, col]
        det_value *= pivot
        push!(pivots, Dict("column" => col, "selected_row" => pivot_row,
                           "swapped" => pivot_row != col, "pivot" => gaussian_json(pivot)))
        for row in (col + 1):n
            if !iszero(M[row, col])
                factor = M[row, col] / pivot
                for j in col:n
                    M[row, j] -= factor * M[col, j]
                end
            end
        end
    end
    if isodd(swaps)
        det_value = -det_value
    end
    det_value, Dict("row_swaps" => swaps, "pivots" => pivots, "singular" => false)
end

function inverse_with_trace(A::Matrix{G})
    n, m = size(A)
    n == m || error("inverse requires square matrix")
    aug = hcat(copy(A), eye_g(n))
    trace = Any[]
    for col in 1:n
        pivot_row_offset = findfirst(row -> !iszero(aug[row, col]), col:n)
        if pivot_row_offset === nothing
            push!(trace, Dict("operation" => "singular", "column" => col))
            return nothing, trace
        end
        pivot_row = col - 1 + pivot_row_offset
        if pivot_row != col
            aug[col, :], aug[pivot_row, :] = copy(aug[pivot_row, :]), copy(aug[col, :])
            push!(trace, Dict("operation" => "swap", "row_a" => col, "row_b" => pivot_row))
        end
        pivot = aug[col, col]
        push!(trace, Dict("operation" => "scale", "row" => col,
                          "divisor" => gaussian_json(pivot)))
        for j in 1:(2n)
            aug[col, j] /= pivot
        end
        for row in 1:n
            row == col && continue
            factor = aug[row, col]
            if !iszero(factor)
                push!(trace, Dict("operation" => "eliminate", "source_row" => col,
                                  "target_row" => row, "factor" => gaussian_json(factor)))
                for j in 1:(2n)
                    aug[row, j] -= factor * aug[col, j]
                end
            end
        end
    end
    aug[:, (n + 1):(2n)], trace
end

function apply_matrix(A::Matrix{G}, x::Vector{G})
    size(A, 2) == length(x) || error("matrix-vector dimension mismatch")
    y = fill(g(0), size(A, 1))
    for i in axes(A, 1)
        for j in axes(A, 2)
            y[i] += A[i, j] * x[j]
        end
    end
    y
end

vector_inner(x::Vector{G}, y::Vector{G}) = sum(conj(xi) * yi for (xi, yi) in zip(x, y); init=g(0))
vector_norm_sq(x::Vector{G}) = vector_inner(x, x)

function rational_json(x::Q)
    Dict("num" => string(numerator(x)), "den" => string(denominator(x)))
end

function gaussian_json(x::G)
    Dict("re" => rational_json(real(x)), "im" => rational_json(imag(x)))
end

matrix_json(A::Matrix{G}) = [[gaussian_json(A[i, j]) for j in axes(A, 2)] for i in axes(A, 1)]
vector_json(x::Vector{G}) = [gaussian_json(v) for v in x]

function json_escape(s::AbstractString)
    io = IOBuffer()
    write(io, '"')
    for c in s
        if c == '"'
            write(io, "\\\"")
        elseif c == '\\'
            write(io, "\\\\")
        elseif c == '\n'
            write(io, "\\n")
        elseif c == '\r'
            write(io, "\\r")
        elseif c == '\t'
            write(io, "\\t")
        elseif Int(c) < 0x20
            write(io, "\\u" * lpad(string(Int(c), base=16), 4, '0'))
        else
            write(io, c)
        end
    end
    write(io, '"')
    String(take!(io))
end

function canonical_json(x)::String
    if x === nothing
        "null"
    elseif x isa Bool
        x ? "true" : "false"
    elseif x isa Integer
        string(x)
    elseif x isa AbstractString
        json_escape(x)
    elseif x isa AbstractVector
        "[" * join((canonical_json(v) for v in x), ",") * "]"
    elseif x isa AbstractDict
        keys_sorted = sort!(collect(keys(x)); by=string)
        "{" * join((json_escape(string(k)) * ":" * canonical_json(x[k]) for k in keys_sorted), ",") * "}"
    else
        error("canonical JSON refuses value of type $(typeof(x))")
    end
end

sha256_hex(bytes::Vector{UInt8}) = bytes2hex(sha256(bytes))
sha256_file(path::AbstractString) = open(path, "r") do io
    bytes2hex(sha256(io))
end

export Q, G, q, g, gq, eye_g, zeros_g, mat_add, mat_sub, mat_scale, mat_mul,
       mat_dagger, mat_commutator, is_zero_matrix, is_hermitian_exact,
       determinant_exact, inverse_with_trace, apply_matrix, vector_inner,
       vector_norm_sq, rational_json, gaussian_json, matrix_json, vector_json,
       canonical_json, sha256_hex, sha256_file

end
