module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2025.Day11

open Std

structure Input where
  names : Array String
  flow : HashMap String (Array String)
deriving BEq, Repr

instance : ToString Input where toString s := s!"{s.names.size}, {s.flow.toList}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_name := alphabets
def parse_line := do
  let node ← parse_name <* pstring ": "
  let outputs ← separated parse_name whitespaces
  pure (node, outputs)

-- #eval AoCParser.parse parse_line "abv: qqq rew "

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
    let ar ← separated parse_line eol
    pure <| Input.mk (ar.iter.map (·.fst) |>.toArray) ar.iter.toHashMap

end parser

namespace Part1

def solve (_ : Input) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2025 11 parser.parse Part1.solve Part2.solve

end Y2025.Day11
