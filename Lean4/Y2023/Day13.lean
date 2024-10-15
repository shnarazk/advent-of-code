import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».BoundedPlane

namespace Y2023.Day13

open Std Accumulation CoP
open TwoDimentionalVector

structure Input where
deriving BEq, Repr
-- instance : ToString Input where toString s := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def maze_line := do
  let v ← many1 ((pchar '.').orElse fun _ ↦ pchar '#') <* many (pchar '\n')
  return v.map (· == '#')

-- #eval AoCParser.parse maze_line "##.#.#"

def maze := many1 maze_line >>= fun m ↦ return BoundedPlane.of2DMatrix m

#eval AoCParser.parse maze "##.#.#\n#....#"

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := return Input.mk

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 13 parser.parse Part1.solve Part2.solve

end Y2023.Day13
