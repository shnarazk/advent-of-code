import Std
import «AoC».Basic

namespace Day02

def collect (_line : String) : Std.HashMap String Nat :=
  Std.HashMap.insert hash "red" 3 
  where 
    hash : Std.HashMap String Nat := Std.HashMap.empty

def solve1_line (line : String) : Nat :=
  0
  where
    hash := collect line

def solve1 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve1_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part1: not yet implemented {lines.size}, {sum}"
  return ()

def solve2 (lines : Array String) : IO Unit := do
  IO.println s!" part1: not yet implemented {lines.size}"
  return ()

end Day02

def day02 : IO Unit := do
  let data ← dataFor 2023 2
  pure data >>= Day02.solve1
  pure data >>= Day02.solve2
