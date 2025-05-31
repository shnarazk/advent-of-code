module AoC
import ParserCombinator
include("Parser.jl")
include("Geometory.jl")
# using .Geometory

const ANS=NamedTuple{(:part1, :part2), Tuple{Int, Int}}

# greet() = print("Hello World!!")

function datafile(year, day)::String
    basedir = ENV["AOC_DIR"]
    days = lpad(string(day), 2, '0')
    seg = basedir * "/data/$(year)/input-day$(days)"
    if 0 < length(ARGS)
        seg *= "-$(ARGS[1])"
    end
    seg * ".txt"
end

# ─── Threaded parallel_map ─────────────────
using Base.Threads            # brings @threads into scope

"""
    parallel_map(f, A::AbstractVector)

Apply `f` to every element of `A` in parallel using Julia’s threads.
Returns a new Vector of results in the same order as `A`.
"""
function parallel_map(f, A::AbstractVector)
    R = Vector{Any}(undef, length(A))
    @threads for i in eachindex(A)
        R[i] = f(A[i])
    end
    return R
end

export ANS, datafile, parallel_map
export Parser # 🔎int, 🔎float, 🔎spaces, 🔎newline, 🔎ints
export Geometory #, within, neighbors4
end # module AoC
