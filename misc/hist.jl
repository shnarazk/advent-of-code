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
xlims = (-5, 15)
ylims = (0, 0.25)
histogram(
    tl,
    xlims=xlims,
    ylims=ylims,
    bins=5,
    normalize=true,
    title="AoC$year execution time distribution",
    xlabel="log2(time[ms])",
    # xlabel="時間",
    ylabel="Frequency",
    legend=false,
    # fontfamily="Noto Sans CJK JP"
    grid=true,
    c=:lightblue,
    framestyle=:box,
    xtickfont=font(12, "Arial"),
    ytickfont=font(12, "Arial"),
    guidefont=font(14, "Arial"),
    titlefont=font(16, "Arial Bold")
)
plot!(
    ktd.x,
    ktd.density,
    xlims=xlims,
    ylims=ylims,
    color=:red,
    linewidth=2,
    label="Density",
    grid=true
)

savefig("hist-$year.png")
run(`pkill -9 gksqt`)
