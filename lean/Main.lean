import «AoC»
import Aesop

def solve1_line (s : String) : Nat :=
  asNum sk.head! * 10 + asNum sk.getLast!
  where
    asNum (c : Char) := c.toNat - '0'.toNat
    sk := s.toList.filter fun c => c.isDigit

#eval solve1_line "aa2aa3"

def solve1 (lines : Array String): IO Unit := do
  let nums := lines.map solve1_line
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!" part1: {sum}"
  return ()

def main : IO Unit := do
  let solver1 := dataFor 2023 1 >>= solve1
  let result ← Aesop.time' solver1
  IO.println s!" => {result.printAsMillis}"
