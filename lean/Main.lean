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

def solve1 (lines : Array String): IO Unit := do
  let nums := lines.map solve1_line
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!" part1: {sum}"
  return ()

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  let lines ← readData "../data/2023/input-day01.txt"
  -- let solver1 := bind (pure lines) solve1
  let solver1 := pure lines >>= solve1
  let result ← Aesop.time' solver1
  IO.println s!" => {result.printAsMillis}"
