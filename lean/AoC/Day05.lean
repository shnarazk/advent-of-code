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

def pseeds := do
  pstring "seeds: " *> sepBy1 number whitespaces <* eol <* eol

def plabel := do
  let _ ← alphabets <* pstring "-to-"
  let _ ← alphabets <* pstring " map:\n"
  return ()

#eval Parsec.run plabel "water-to-light map:\n"

def range := do
  let d ← number <* separator ' '
  let s ← number <* separator ' '
  let r ← number <* separator₀ ' '
  return ({ dest := d, source := s, span := r } : Range)

def pmap := sepBy1 range eol

#eval Parsec.run pmap "88 18 7"
#eval Parsec.run pmap "88 18 7\n18 25 70"

-- def parser : Parsec Range := (plabel *> range)
def parser : Parsec ((Array Nat) × (Array (Array Range))) := do
  let ss ← pseeds
  let ms ← sepBy1 (plabel *> pmap) (pstring "\n\n")
  return (ss, ms)

#eval Parsec.run parser "seeds: 2 5\n\na-to-b map:\n88 18 7"

def parse (data : String) :=
  match Parsec.run parser data with
  | Except.ok ret  => some ret
  | Except.error _ => none

#eval parse "seeds: 1\n\na-to-b map:\n0 1 2"

end parser

def transpose₀ (pos : Nat) (rs : List Range) : Nat :=
  match rs with
  | [] => pos
  | List.cons range rs' =>
      if range.source ≤ pos && pos < range.source + range.span
      then range.dest + pos - range.source
      else transpose₀ pos rs'

def transpose (seeds : Array Nat) (rs : Array Range) :=
  Array.map (fun seed => transpose₀ seed (Array.toList rs)) seeds

def solve1 (data : String) : IO Unit := do
  match parser.parse data with
  | some (seeds, maps) =>
    let point : Array Nat := Array.foldl transpose seeds maps
    IO.println s!" part1: {point.minD 0}"
  | _ => IO.println s!" part1: parse error"
  return ()

def solve2_line (_line : String) : Nat :=
  0

def solve2 (data : String) : IO Unit := do
  match parser.parse data with
  | some _ =>
    IO.println s!" part2: not yet implemented"
  | _ => IO.println s!" part1: parse error"
  return ()

end Day05

def day05 : IO Unit := do
  let data ← dataOf 2023 5
  pure data >>= Day05.solve1
  -- pure data >>= Day05.solve2
