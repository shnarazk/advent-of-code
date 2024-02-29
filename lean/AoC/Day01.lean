import Std
import «AoC».Basic

namespace Day01

def solve1_line (s : String) : Nat :=
  asNum sk.head! * 10 + asNum sk.getLast!
  where
    asNum (c : Char) := c.toNat - '0'.toNat
    sk := s.toList.filter fun c => c.isDigit

#eval solve1_line "aa2aa3"

def solve1 (lines : Array String) : IO Unit := do
  let nums := lines.map solve1_line
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!" part1: {sum}"
  return ()

def solve2 (lines : Array String) : IO Unit := do 
  IO.println s!" part2: not yet implemented: {lines.size}"
  return ()

end Day01

def day01 : IO Unit := do
  let data ← dataFor 2023 1
  pure data >>= Day01.solve1
  pure data >>= Day01.solve2
