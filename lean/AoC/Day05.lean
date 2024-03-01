import Std
import «AoC».Basic

namespace Day05

def parsed (source : String) : sorry := sorry

def solve1_line (line : String) : Nat :=
  sorry

#eval solve1_line ""

def solve1 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve1_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part1: {sum}"
  return ()

def solve2_line (line : String) : Nat :=
  sorry

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
