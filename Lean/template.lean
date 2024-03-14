import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Day??
open Std Accumulation CoP

--structure Data where
--  new ::
--deriving Repr
-- instance : ToString Data where
--   toString s := s!"[{s._beg},{s._end}]"

namespace parser
open Lean.Parsec AoCParser

def parser := sepBy1 number whitespaces

end parser

namespace part1

def solve (_data : Data) : Nat := 0

end part1

namespace part2

def evaluate (_line : Data) : Nat := 0

-- #eval evaluate ""

def solve (data : Array Data) : IO Nat := do
  return sum $ data.map evaluate

end part2

end Day??

def day?? (ext : Option String) : IO Answers := do
  let data ← dataOf 2023 ?? ext
  let _lines ← linesOf 2023 ?? ext
  if let some d := AoCParser.parse Day??.parser.parser data
    then return (s!"{← Day??.part1.solve data}", s!"←{← Day??.part2.solve lines}")
    else return ("parse error", "")
