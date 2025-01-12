using Pkg
# Pkg.add("Graphs")
# Pkg.add("GraphPlot")
# Pkg.add("Colors")
# Pkg.add("Cairo")
using Graphs
using Cairo
using GraphPlot
using Colors
using Compose
using JSON

# Load the JSON file
json_path = "day24.json"
json_data = JSON.parsefile(json_path)

label_to_number = Dict{String,Int}()

function update_label_to_number!(label)
    if !haskey(label_to_number, label)
        label_to_number[label] = length(label_to_number) + 1
    end
end
function get_label_number(label::String)::Int
    return label_to_number[label]
end

for gate in json_data
    update_label_to_number!(gate[1])
    if 2 <= length(gate[2])
        for wire in gate[2]
            update_label_to_number!(wire)
        end
    end
end
sorted_labels = sort(collect(label_to_number), by=x -> x[2]) |> x -> map(y -> y[1], x)

# Create a directed graph
g = DiGraph()
add_vertices!(g, length(sorted_labels))

for edge in json_data
    if 2 <= length(edge[2])
        add_edge!(g, get_label_number(edge[2][1]), get_label_number(edge[1]))
        add_edge!(g, get_label_number(edge[2][2]), get_label_number(edge[1]))
    end
end

# Plot the graph
layout = (args...) -> spring_layout(args...; C=30)
draw(
    PNG("test.png"),
    gplot(
        g,
        # layout=layout,
        # layout=stressmajorize_layout,
        # linetype="curve",
        # nodelabel=sorted_labels,
        nodesize=0.05,
        arrowlengthfrac=0.04,
    )
)
