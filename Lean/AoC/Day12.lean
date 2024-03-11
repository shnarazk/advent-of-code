import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Day12
open Std Accumulation CoP

structure Data where
  new ::
  pattern : Array Char
  rule    : Array Nat
deriving Repr

instance : ToString Data where
  toString s := s!"[{s.pattern},{s.rule}]"

namespace parser
open Lean.Parsec AoCParser

def pcell := pchar '.' <|> pchar '#' <|> pchar '?'

def line_parser := do
  let pattern ← many1 pcell <* whitespaces
  let rule    ← sepBy1 number (pchar ',')
  return Data.new pattern rule 

def parser := sepBy1 line_parser eol

end parser

namespace part1

def solve (data : String) : IO Unit := do
  if let some d := AoCParser.parse parser.parser data then
  IO.println s!"  part1: {d}"

end part1

namespace part2

def solve2_line (_line : String) : Nat := 0

-- #eval solve2_line ""

def solve (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  IO.println s!"  part2: {sum points}"

end part2

end Day12

def day12 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 12 ext
  let lines ← linesOf 2023 12 ext
  Day12.part1.solve data
  Day12.part2.solve lines
