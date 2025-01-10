#!/usr/bin/env julia
import Pkg
# Pkg.add("JSON")
# Pkg.add("Plots")
# Pkg.add("GridVisualize")
Pkg.add("Colors")
Pkg.add("Images")
using JSON, Plots # , GridVisualize
using Colors, Images

serialized = read("2024/day18.json", String)
data = JSON.parse(serialized)
grid_data = data["line"]
# Extract dimensions of the grid
rows = 1 + maximum([g[1] for g in grid_data])
cols = 1 + maximum([g[2] for g in grid_data])
println(rows)
println(cols)
# Create an empty matrix for plotting purposes

grid_matrix = fill(:white, rows, cols)

# Populate the grid matrix with :black or :white based on grid data values
for g in grid_data
    grid_matrix[g[1]+1, g[2]+1] = :black
end

color_map = Dict(:white => RGB(1.0, 1.0, 1.0), :black => RGB(0.0, 0.0, 0.0))
color_matrix = [color_map[element] for element in grid_matrix]

mosaicview(color_matrix)
# Plot the grid using Plots package
# gridplot(grid_matrix,
    # xlims=(0.5, cols + 0.5),
    # ylims=(0.5, rows + 0.5),
    # aspect_ratio=:equal,
    # markerstrokecolor=(:black, :white)[1],
    # markersize=10,
    # legend=false
# )
# plot!(
#     ktd.x,
#     ktd.density,
#     ylims=(0, 0.4),
#     color=:red,
#     linewidth=2)

# savefig("hist2024.png")
