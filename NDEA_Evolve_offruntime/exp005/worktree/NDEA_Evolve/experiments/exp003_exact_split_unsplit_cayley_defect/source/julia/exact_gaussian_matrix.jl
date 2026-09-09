module ExactGaussianMatrix

using SHA

const Q = Rational{BigInt}
const G = Complex{Q}

q(n::Integer, d::Integer=1) = Q(BigInt(n), BigInt(d))
g(re::Integer, im::Integer=0) = G(q(re), q(im))
gq(re::Q, im::Q=q(0)) = G(re, im)

function eye_g(n::Int)
    result = fill(g(0), n, n)
    for index in 1:n
        result[index, index] = g(1)
    end
    result
end

zeros_g(rows::Int, columns::Int) = fill(g(0), rows, columns)

function mat_add(A::Matrix{G}, B::Matrix{G})
    size(A) == size(B) || error("matrix dimension mismatch in add")
    result = similar(A)
    for row in axes(A, 1), column in axes(A, 2)
        result[row, column] = A[row, column] + B[row, column]
    end
    result
end

function mat_sub(A::Matrix{G}, B::Matrix{G})
    size(A) == size(B) || error("matrix dimension mismatch in subtract")
    result = similar(A)
    for row in axes(A, 1), column in axes(A, 2)
        result[row, column] = A[row, column] - B[row, column]
    end
    result
end

function mat_scale(coefficient::G, A::Matrix{G})
    result = similar(A)
    for row in axes(A, 1), column in axes(A, 2)
        result[row, column] = coefficient * A[row, column]
    end
    result
end

function mat_mul(A::Matrix{G}, B::Matrix{G})
    size(A, 2) == size(B, 1) || error("matrix dimension mismatch in multiply")
    result = zeros_g(size(A, 1), size(B, 2))
    for row in axes(A, 1), column in axes(B, 2)
        total = g(0)
        for index in axes(A, 2)
            total += A[row, index] * B[index, column]
        end
        result[row, column] = total
    end
    result
end

function mat_dagger(A::Matrix{G})
    result = zeros_g(size(A, 2), size(A, 1))
    for row in axes(A, 1), column in axes(A, 2)
        result[column, row] = conj(A[row, column])
    end
    result
end

is_zero_matrix(A::Matrix{G}) = all(iszero, A)
is_hermitian_exact(A::Matrix{G}) =
    size(A, 1) == size(A, 2) && A == mat_dagger(A)

function inverse_with_trace(A::Matrix{G})
    n, m = size(A)
    n == m || error("inverse requires square matrix")
    augmented = hcat(copy(A), eye_g(n))
    trace = Any[]
    for column in 1:n
        offset = findfirst(row -> !iszero(augmented[row, column]), column:n)
        if offset === nothing
            push!(trace, Dict("operation" => "singular", "column" => column))
            return nothing, trace
        end
        pivot_row = column - 1 + offset
        if pivot_row != column
            augmented[column, :], augmented[pivot_row, :] =
                copy(augmented[pivot_row, :]), copy(augmented[column, :])
            push!(trace, Dict("operation" => "swap", "row_a" => column,
                              "row_b" => pivot_row))
        end
        pivot = augmented[column, column]
        push!(trace, Dict("operation" => "scale", "row" => column,
                          "divisor" => gaussian_json(pivot)))
        for index in 1:(2n)
            augmented[column, index] /= pivot
        end
        for row in 1:n
            row == column && continue
            factor = augmented[row, column]
            if !iszero(factor)
                push!(trace, Dict("operation" => "eliminate", "source_row" => column,
                                  "target_row" => row,
                                  "factor" => gaussian_json(factor)))
                for index in 1:(2n)
                    augmented[row, index] -= factor * augmented[column, index]
                end
            end
        end
    end
    augmented[:, (n + 1):(2n)], trace
end

function rational_json(value::Q)
    Dict("num" => string(numerator(value)), "den" => string(denominator(value)))
end

function gaussian_json(value::G)
    Dict("re" => rational_json(real(value)), "im" => rational_json(imag(value)))
end

matrix_json(A::Matrix{G}) =
    [[gaussian_json(A[row, column]) for column in axes(A, 2)]
     for row in axes(A, 1)]

function json_escape(value::AbstractString)
    output = IOBuffer()
    write(output, '"')
    for character in value
        if character == '"'
            write(output, "\\\"")
        elseif character == '\\'
            write(output, "\\\\")
        elseif character == '\n'
            write(output, "\\n")
        elseif character == '\r'
            write(output, "\\r")
        elseif character == '\t'
            write(output, "\\t")
        elseif Int(character) < 0x20
            write(output, "\\u" * lpad(string(Int(character), base=16), 4, '0'))
        else
            write(output, character)
        end
    end
    write(output, '"')
    String(take!(output))
end

function canonical_json(value)::String
    if value === nothing
        "null"
    elseif value isa Bool
        value ? "true" : "false"
    elseif value isa Integer
        string(value)
    elseif value isa AbstractString
        json_escape(value)
    elseif value isa AbstractVector
        "[" * join((canonical_json(item) for item in value), ",") * "]"
    elseif value isa AbstractDict
        ordered_keys = sort!(collect(keys(value)); by=string)
        "{" * join((json_escape(string(key)) * ":" * canonical_json(value[key])
                    for key in ordered_keys), ",") * "}"
    else
        error("canonical JSON refuses value of type $(typeof(value))")
    end
end

sha256_hex(bytes::Vector{UInt8}) = bytes2hex(sha256(bytes))
sha256_file(path::AbstractString) = open(path, "r") do stream
    bytes2hex(sha256(stream))
end

export Q, G, q, g, gq, eye_g, zeros_g, mat_add, mat_sub, mat_scale, mat_mul,
       mat_dagger, is_zero_matrix, is_hermitian_exact, inverse_with_trace,
       rational_json, gaussian_json, matrix_json, canonical_json, sha256_hex,
       sha256_file

end
