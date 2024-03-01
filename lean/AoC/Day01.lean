import Std
import «AoC».Basic

namespace Day01

def solve1_ (s : List Char) : Nat :=
  asNum sk.head! * 10 + asNum sk.getLast!
  where
    asNum (c : Char) := c.toNat - '0'.toNat
    sk := s.filter Char.isDigit

#eval solve1_ "aa2aa3".toList

def solve1 (lines : Array String) : IO Unit := do
  let nums := lines.map (fun (s) => solve1_ s.toList)
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!" part1: {sum}"
  return ()

#eval List.filterMap (fun x => if 2 < x then some x else none) [5, 2, 0, 3]

def mnemonic (s : String) : Char :=
  if s.startsWith "one"
  then '1'
  else if s.startsWith "two"
  then '2'
  else if s.startsWith "three"
  then '3'
  else if s.startsWith "four"
  then '4'
  else if s.startsWith "five"
  then '5'
  else if s.startsWith "six"
  then '6'
  else if s.startsWith "seven"
  then '7'
  else if s.startsWith "eight"
  then '8'
  else if s.startsWith "nine"
  then '9'
  else s.get! 0

def solve2_ (s : String) : Nat :=
  solve1_ ((List.map (fun n => s.drop n) (List.range s.length)).map mnemonic)

def solve2 (lines : Array String) : IO Unit := do
  let nums := lines.map solve2_
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!" part2: {sum}"
  return ()

end Day01

def day01 : IO Unit := do
  IO.println s!"{List.range 10}"
  let data ← dataFor 2023 1
  pure data >>= Day01.solve1
  pure data >>= Day01.solve2
