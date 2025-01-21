#!/usr/bin/env Rscript

library(jsonlite)
library(ggplot2)

j <- fromJSON("2024/execution_time.json")

p <- ggplot(j, aes(x = time))  + geom_histogram(aes(y = after_stat(density)), binwidth = 100, fill = "blue", color="black")  + labs(title = "AoC2024", x = "time", y = "freq")  + geom_density(color = "red", linewidth = 1)

cat("ooo")

ggsave("hist-by-R.png", plot = p, width = 6, height = 4)
