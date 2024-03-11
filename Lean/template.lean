import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day??
open Std Accumulation

-- structure Data where
--deriving Repr
-- instance : ToString Data where
--   toString s := s!"[{s._beg},{s._end}]"

namespace parser
open Lean.Parsec AoCParser

def parser := sepBy1 number whitespaces

end parser

namespace part1

def solve (data : String) : IO Unit := do
  if let some d := AoCParser.parse parser.parser data then
  IO.println s!"  part1: {d.size}"

end part1

namespace part2

def solve2_line (_line : String) : Nat := 0

-- #eval solve2_line ""

def solve (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  IO.println s!"  part2: {sum points}"

end part2

end Day??

def day?? (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 ?? ext
  let lines ← linesOf 2023 ?? ext
  Day??.part1.solve data
  Day??.part2.solve lines
