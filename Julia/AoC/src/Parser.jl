module Parser

using ParserCombinator
export 🔎int, 🔎float, 🔎spaces, 🔎newline, 🔎ints

"""
🔎int

Parser that matches one or more digits (`\\d+`) and converts the matched string to an `Int`.
"""
🔎int = PInt()

"""
🔎float

Parser that matches a floating-point number (one or more digits, a dot, and zero or more digits, `\\d+\\.\\d*`) and converts the matched string to a `Float64`.
"""
🔎float = PFloat64()

"""
🔎spaces

Parser that consumes zero or more space or tab characters (`[ \t]*`) and drops them from the result.
"""
🔎spaces = Drop(p"[ \t]*")

"""
🔎newline

Parser that consumes a single newline character (`\n`) and drops it from the result.
"""
🔎newline = Drop(p"\n")

"""
🔎ints

Parser that repeatedly matches integers separated by optional spaces, collecting the results into a vector of `Int` values.
"""
🔎ints = Repeat(🔎int + 🔎spaces)

end
