import Std
import «AoC».Basic

namespace Day0?

def parsed (_source : String) : Nat := 0

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

end Day0?

def day0? : IO Unit := do
  let data ← dataFor 2023 ?
  pure data >>= Day0?.solve1
  pure data >>= Day0?.solve2
