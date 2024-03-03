import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day0?
open Std

-- structure Data where
--deriving Repr

namespace parser
open Lean.Parsec

def parser := sorry

end parser

def solve1 (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some d => IO.println s!"  part1: {d.size}"
  return ()

def solve2_line (_line : String) : Nat := 0

-- #eval solve2_line ""

def solve2 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!"  part2: {sum}"
  return ()

end Day0?

def day0? (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 ? ext
  let lines ← linesOf 2023 ? ext
  pure data >>= Day0?.solve1
  pure lines >>= Day0?.solve2
