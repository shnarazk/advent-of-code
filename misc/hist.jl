#!/usr/bin/env julia
# import Pkg
# Pkg.add("JSON")
# Pkg.add("KernelDensity")
# Pkg.add("Plots")
using JSON, KernelDensity, Plots

# get command line argument and store it to variable 'year'
const year = ARGS[1]

execution_data = read("$year/execution_time.json", String)
data = JSON.parse(execution_data)
times = [item["time"] for item in data if haskey(item, "time")]
tl = log2.(times)
ktd = kde(tl)

histogram(
    tl,
    xlims=(-5, 20),
    ylims=(0, 0.4),
    bins=20,
    normalize=true,
    title="AoC$year execution time distribution",
    xlabel="log2(time[ms])",
    # xlabel="時間",
    ylabel="Freq",
    legend=false,
    # fontfamily="Noto Sans CJK JP"
)
plot!(
    ktd.x,
    ktd.density,
    ylims=(0, 0.4),
    color=:red,
    linewidth=2)

savefig("hist-$year.png")
