#!/usr/bin/env julia
# using Pkg
# Pkg.add("DrawSimpleGraphs")
# Pkg.add("Plots")
# Pkg.add("SimpleGraphs")
using DrawSimpleGraphs, JSON, Plots, SimpleGraphs

# Load the JSON file
json_path = "day14.json"
json_data = JSON.parsefile(json_path)
ema = log.(json_data["ema"])
trend = log.(json_data["trend"])
println(ema[1000:1020])
println(trend[1000:1020])
ylim = (-2.0, 2.0)
plot(
    ema,
    ylim = ylim,
    label = "Isolated point ratio (EMA decay rate = 0.9)",
    xlabel = "Iteration",
    ylabel = "ln(Value)",
    title = "AoC2024 Day 14, definition of meaningful picture",
    grid = true,
)

plot!(
    trend,
    label = "Trend",
)

savefig("day14-ema.png")
