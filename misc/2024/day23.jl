# using Pkg
# Pkg.add("SimpleGraphs")
# Pkg.add("DrawSimpleGraphs")
# Pkg.add("Plots")

using JSON
using SimpleGraphs
using DrawSimpleGraphs
using Plots

# Load the JSON file
json_path = "day23.json"
json_data = JSON.parsefile(json_path)

# Initialize a graph
g = UndirectedGraph()

# Add edges from JSON data
for edge in json_data
    add!(g, edge[1], edge[2])
end

# Plot the graph
embed(g, :spring)
set_vertex_size(g, 1)
draw(
    g,
)
savefig("day23.png")
