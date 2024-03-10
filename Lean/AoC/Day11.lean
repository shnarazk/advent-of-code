import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day11
open Std

structure Data where
  new   ::
  size  : Nat × Nat
  array : Array Bool
deriving Repr

namespace Data

#eval #[false, false, true, false].size
#eval Data.new (2, 2) #[false, false, true, false]

instance : ToString Data where
  toString s := s!"({toString s.size})[{toString s.array}]"

end Data

namespace parser
open Lean.Parsec AoCParser

def pcell := (pchar '.' *> return false) <|> (pchar '#' *> return true)
def parser := do
  let a ← sepBy1 (many1 pcell) eol
  return Data.new (a.size, a[0]!.size) (Array.join a)

end parser

namespace part1
def solve (data : String) : IO Unit := do
  if let some d := dbgTraceVal $ AoCParser.parse parser.parser data then
    IO.println s!"  part1: {d}"

end part1

namespace part2

def solve2_line (_line : String) : Nat := 0

-- #eval solve2_line ""

def solve (data : String) : IO Unit := do
  if let some d := AoCParser.parse parser.parser data then
    IO.println s!"  part2: {d.size}"

end part2

end Day11

def day11 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 11 ext
  Day11.part1.solve data
  Day11.part2.solve data
