module AoCParser
using ParserCombinator
export pint, pfloat, pspaces, pnewline

pint = p"\d+" > s -> parse(Int, s)
pfloat = p"\d+\.\d*" > s -> parse(Float64, s)
pspaces = Drop(p"[ \t]*")
pnewline = Drop(p"\n")
end
