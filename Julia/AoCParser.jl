module AoCParser

using ParserCombinator
export 🔎int, 🔎float, 🔎spaces, 🔎newline, 🔎ints

🔎int = PInt()       # p"\d+" > s -> parse(Int, s)
🔎float = PFloat64() # p"\d+\.\d*" > s -> parse(Float64, s)
🔎spaces = Drop(p"[ \t]*")
🔎newline = Drop(p"\n")
🔎ints = Repeat(🔎int + 🔎spaces)

end
