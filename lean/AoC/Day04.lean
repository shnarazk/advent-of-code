import Std
import «AoC».Basic

namespace Day04

def parsed (source : String) : List Nat × List Nat :=
  (toNats targets, toNats cands)
  where
    body := List.getD (String.split source (. == ':')) 1 ""
    parts := String.split body (. == '|')
    targets := List.getD parts 0 "no num"
    cands := List.getD parts 1 "no name"
    toNats := fun (s : String) =>
      let pair := String.split s.trim (. == ' ')
      let numbers := List.filter (fun s => s != "") pair
      List.map String.toNat! numbers

#eval parsed "Card 1: 41 48 | 83  1 41"

def solve1_line (_line : String) : Nat := 0

def solve1 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve1_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part1: {sum}"
  return ()

def solve2_line (_line : String) : Nat := 0

def solve2 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part1: {sum}"
  return ()

end Day04

def day04 : IO Unit := do
  let data ← dataFor 2023 4
  pure data >>= Day04.solve1
  pure data >>= Day04.solve2
