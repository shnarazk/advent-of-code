#!/usr/bin/env julia
import Pkg
# Pkg.add("JSON"),
# Pkg.add("Plots"),
# Pkg.add("GridVisualize"),
# Pkg.add("Colors"),
using JSON, Plots, Colors

grid_data = JSON.parse(read("2024/day18.json", String))["line"]

# Extract dimensions of the grid
rows = 1 + maximum([g[1] for g in grid_data])
cols = 1 + maximum([g[2] for g in grid_data])
len = length(grid_data)

# Create an empty matrix for plotting purposes
grid_matrix = fill(RGB(1.0, 1.0, 1.0), rows, cols)
for (i, g) in enumerate(grid_data)
    c = (len - i) / len
    grid_matrix[g[1]+1, g[2]+1] = RGB(c, c, c)
end
grid_matrix[1, 1] = RGB(1.0, 0.0, 0.0)

# color_map = Dict(
#     :red => RGB(1.0, 0.0, 0.0),
#     :white => RGB(1.0, 1.0, 1.0),
#     :black => RGB(0.0, 0.0, 0.0),
# )
# color_matrix = [color_map[element] for element in grid_matrix]

heatmap(
    # color_matrix,
    grid_matrix,
    title="Y2024 day18",
    aspect_ratio=:equal
)
savefig("day18-grid.png")
