#!/usr/bin/env julia
# This file reads "day10.json", constructs a color-coded grid, and saves a plot

import Pkg
# Pkg.add("JSON"),
# Pkg.add("Plots"),
# Pkg.add("GridVisualize"),
# Pkg.add("Colors"),
using JSON, Plots, Colors

grid_data = JSON.parse(read("day10.json", String))

rows = length(grid_data)
cols = length(grid_data[1])
len = rows * cols

grid_matrix = fill(RGB(1.0, 1.0, 1.0), rows, cols)

for (i, g) in enumerate(grid_data)
    for (j, c) in enumerate(g)
        v = if c
            RGB(1.0, 1.0, 1.0)
        else
            RGB(0.0, 0.0, 0.0)
        end
        grid_matrix[i, j] = v
    end
end

# Plots.default(size=(1000, 800))
heatmap(
    # color_matrix,
    grid_matrix,
    title="Y2023 day10",
    aspect_ratio=:equal,
    size=(rows * 3 + 100, cols * 3 + 100)
)
savefig("day10-grid.png")
