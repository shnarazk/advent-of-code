#!/usr/bin/env julia
# Warmup script for PackageCompiler precompilation.
#
# This file is executed during sysimage creation when passed as:
#   --warmup=Julia/scripts/warmup.jl
#
# Goal:
# - Exercise common code paths so Julia records and caches method specializations.
# - Keep it fast, deterministic, and side-effect free.
#
# Tips:
# - Avoid I/O, network, or large allocations.
# - Keep runtime well under a few seconds.
# - Focus on "hot" functions you use frequently.

function _warmup()
    println("Warmup: starting")

    # Try to load your AoC utilities. The project depends on AoC via [sources] in Project.toml.
    # We guard this so the warmup never aborts the build if optional code changes.
    try
        @eval using AoC
        println("Warmup: AoC loaded")

        # Lightly exercise parallel_map with small input.
        # This helps precompile threading and simple closures.
        local v = collect(1:8)
        local r1 = AoC.parallel_map(x -> x + 1, v)
        # Do a couple of variations to generate a few more specializations.
        local r2 = AoC.parallel_map(x -> x * x, v)
        local r3 = AoC.parallel_map(identity, v)

        # Use results so the optimizer can't trivially DCE everything.
        # Keep the output short to avoid noise in CI logs.
        println("Warmup: parallel_map results: ", (r1[1], r2[1], r3[1]))

        # Optional: explicitly request precompilation for common signatures.
        # These are best-effort; they won't error if a method isn't found.
        try
            Base.precompile(AoC.parallel_map, (Function, Vector{Int}))
            Base.precompile(AoC.parallel_map, (Function, Vector{Any}))
        catch preerr
            println("Warmup: precompile hints failed (non-fatal): ", preerr)
        end
    catch err
        println("Warmup: skipping AoC warmup (non-fatal): ", err)
    end

    # Add more light-touch warmups here for other packages/APIs you rely on frequently.
    # Example pattern:
    # try
    #     using SomePkg
    #     x = SomePkg.do_small_thing(42)
    #     Base.precompile(SomePkg.do_small_thing, (Int,))
    # catch err
    #     println("Warmup: SomePkg skipped: ", err)
    # end

    println("Warmup: done")
    return nothing
end

# Run when invoked as a script.
_warmup()
