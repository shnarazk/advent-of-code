module AoC
import ParserCombinator
include("Parser.jl")
include("Geometry.jl")
include("Dir.jl")
include("Math.jl")

const ANS = NamedTuple{(:part1, :part2),Tuple{Int,Int}}

"""
    datafile(year, day)::String

    Return the path to the Advent of Code input file for `year` and `day`.

    The base directory is taken from the environment variable `AOC_DIR`. The file
    name is constructed as:

    `\$AOC_DIR/data/<year>/input-day<DD>[ -<suffix> ].txt`

    where `<DD>` is `day` left-padded to two digits. If an extra command-line
    argument is provided (i.e. `length(ARGS) > 0`), it is appended as a suffix
    (e.g. `-test`) before the `.txt` extension, which is useful for selecting
    alternate inputs.

    # Examples
    ```julia
    ENV["AOC_DIR"] = "/home/me/aoc"
    datafile(2023, 1)   # "/home/me/aoc/data/2023/input-day01.txt"

    # with `ARGS = ["test"]`
    datafile(2023, 1)   # "/home/me/aoc/data/2023/input-day01-test.txt"
    ```

    # Errors
    Throws a `KeyError` if `ENV["AOC_DIR"]` is not set.
"""
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
export Parser
export Geometry
export Dir
export Math

end
