#!/usr/bin/env Rscript
library(jsonlite)
library(igraph)
library(ggplot2)

j <- fromJSON("2024/day24.json")
r <- Filter(function(l) length(l[[2]]) == 2, j) 
data <- lapply(
    r,
    function(l) {
      list(
        list(from = l[[2]][[1]], to = l[[1]]), list(from = l[[2]][[2]], to = l[[1]])
    )})
data <- unlist(data, recursive = FALSE)
# print(sapply(data, function (l) l[[1]]))
dataframe <- data.frame(
  list(
    from = unlist(sapply(data, function (l) l[[1]])),
    to   = unlist(sapply(data, function (l) l[[2]]))
  )
)
# print(dataframe)
g <- graph_from_data_frame(dataframe, directed = TRUE)
l <- layout_nicely(g)
png("day24-by-R.png")
p <- plot(g, layout = l, edge.arrow.size = .3, vertex.size = 4, vertex.label=NA)
dev.off()
