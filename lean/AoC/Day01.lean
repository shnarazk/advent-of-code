import Std
import «AoC».Basic

namespace Day01

def solve1_ (s : List Char) : Nat :=
  asNum sk.head! * 10 + asNum sk.getLast!
  where
    asNum (c : Char) := c.toNat - '0'.toNat
    sk := s.filter Char.isDigit

-- #eval solve1_ "aa2aa3".toList

def solve1 (lines : Array String) : IO Unit := do
  let nums := lines.map (fun (s) => solve1_ s.toList)
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!"  part1: {sum}"

-- #eval List.filterMap (fun x => if 2 < x then some x else none) [5, 2, 0, 3]

def mnemonic (s : List Char) : Char :=
  if      (String.toList "one").isPrefixOf s   then '1'
  else if (String.toList "two").isPrefixOf s   then '2'
  else if (String.toList "three").isPrefixOf s then '3'
  else if (String.toList "four").isPrefixOf s  then '4'
  else if (String.toList "five").isPrefixOf s  then '5'
  else if (String.toList "six").isPrefixOf s   then '6'
  else if (String.toList "seven").isPrefixOf s then '7'
  else if (String.toList "eight").isPrefixOf s then '8'
  else if (String.toList "nine").isPrefixOf s  then '9'
  else s.get! 0

def solve2_ (s : String) : Nat :=
  solve1_ ((List.takeWhile (. != []) s.toList.tails).map mnemonic)

-- #eval ((List.takeWhile (. != []) (List.tails (String.toList "two3four"))).map mnemonic)

def solve2 (lines : Array String) : IO Unit := do
  let nums := lines.map solve2_
  let sum := Array.foldl (. + .) 0 nums
  IO.println s!"  part2: {sum}"

end Day01

-- def train {m : Type u₁ → Type u₂} {β₁ β₂ : Type u₁} (a : α → m β₁) (b : α → m β₂) : α → m β₂ :=
--   fun (x : α) => a x >>= (fun _ => b x)

def day01 (alt : Option String): IO Unit := do
  let data ← linesOf 2023 1 alt
  Day01.solve1 data
  Day01.solve2 data
