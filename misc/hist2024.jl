#!/usr/bin/env julia
# import Pkg
# Pkg.add("JSON")
# Pkg.add("Plots")
using JSON
using Plots

data2024 = read("2024/execution_time.json", String)
data = JSON.parse(data2024)
times = [item["time"] for item in data if haskey(item, "time")]
tl = log2.(times)

# histogram(tl, xlims=(-2, 20), bins=10, title="AoC2024", xlabel="時間", ylabel="Freq", legend=false, fontfamily="Noto Sans CJK JP")
histogram(tl, xlims=(-2, 20), bins=10, title="AoC2024", xlabel="time", ylabel="Freq", legend=false)
savefig("hist2024.png")
