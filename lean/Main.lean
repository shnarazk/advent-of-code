import «AoC»
import Std.Data.String
import Std.Data.List
import Std.Data.Nat

def readData (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

def solve1 (s : String) : Nat :=
  (sk.head!.toNat - '0'.toNat) * 10 + (sk.getLast!.toNat - '0'.toNat)
  where
    sk := s.toList.filter fun c => c.isDigit

#eval solve1 "aa2aa3"

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  let lines ← readData "../data/2023/input-day01.txt"
  let output := lines.map solve1
  -- IO.println s!" => {lines}"
  IO.println s!" => {output}"
  let sum := Array.foldl (. + .) 0 output
  IO.println s!" => {sum}"
