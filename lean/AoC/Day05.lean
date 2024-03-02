import Std
import «AoC».Basic
import «AoC».Parser
import Lean.Data.Parsec

namespace Day05

structure Range where
  dest   : Nat
  source : Nat
  span   : Nat
deriving Repr

namespace parser
open Lean Parsec

def plabel := do
  let _ ← many1Chars asciiLetter <* pstring "-to-"
  let _ ← many1Chars asciiLetter <* pchar ' '
  let _ ← pstring "map:"
  return ()

#eval Parsec.run plabel "water-to-light map:"

def range := do
  let r ← number <* separator ' '
  let d ← number <* separator ' '
  let s ← number <* separator₀ ' '
  return ({ dest := d, source := s, span := r } : Range)

def pmap := manySep range eol

#eval Parsec.run pmap "88 18 7\n18 25 70"

def parser : Parsec (Array Range) := manySep (plabel *> range) (pstring "\n\n")

def parse (data : String) := Parsec.run parser data

end parser

def solve1_line (_line : String) : Nat :=
  0

#eval solve1_line ""

def solve1 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve1_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part1: {sum}"
  return ()

def solve2_line (_line : String) : Nat :=
  0

def solve2 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part2: {sum}"
  return ()

end Day05

def day05 : IO Unit := do
  let data ← dataFor 2023 5
  pure data >>= Day05.solve1
  pure data >>= Day05.solve2
