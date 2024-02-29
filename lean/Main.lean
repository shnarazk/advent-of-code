import «AoC»
import Aesop
import Std.Data.String
import Std.Data.List
import Std.Data.Nat

def readData (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

def solve1_line (s : String) : Nat :=
  (sk.head!.toNat - '0'.toNat) * 10 + (sk.getLast!.toNat - '0'.toNat)
  where
    sk := s.toList.filter fun c => c.isDigit

#eval solve1_line "aa2aa3"

def solve1 : IO Unit := do
  let lines ← readData "../data/2023/input-day01.txt"
  -- IO.println s!" => {lines}"
  let nums := lines.map solve1_line
  -- IO.println s!" => {nums}"
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!" part1: {sum}"
  return ()

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  let result ← Aesop.time' solve1
  IO.println s!" => {result.printAsMillis}"
