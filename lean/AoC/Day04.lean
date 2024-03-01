import Std
import «AoC».Basic

namespace Day04

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
