import Std
import «AoC».Basic

namespace Day01
open Accumulation

namespace Part1

def evaluate (s : List Char) : Nat :=
  let asNum (c : Char) : Nat := c.toNat - '0'.toNat
  let sk := s.filter Char.isDigit
  asNum sk.head! * 10 + asNum sk.getLast!

def solve (lines : Array String) : IO (Array String) := do
  let nums := lines.map (fun (s) => evaluate s.toList)
  IO.println s!"  part1: {sum nums}"
  return lines

end Part1

namespace Part2

def mnemonic (s : List Char) : Char :=
  if      (String.toList "one"  ).isPrefixOf s then '1'
  else if (String.toList "two"  ).isPrefixOf s then '2'
  else if (String.toList "three").isPrefixOf s then '3'
  else if (String.toList "four" ).isPrefixOf s then '4'
  else if (String.toList "five" ).isPrefixOf s then '5'
  else if (String.toList "six"  ).isPrefixOf s then '6'
  else if (String.toList "seven").isPrefixOf s then '7'
  else if (String.toList "eight").isPrefixOf s then '8'
  else if (String.toList "nine" ).isPrefixOf s then '9'
  else s.get! 0

def solve (lines : Array String) : IO Unit := do
  let nums := lines.map (fun s =>
    (List.takeWhile (. != []) s.toList.tails).map mnemonic
    |> Part1.evaluate)
  IO.println s!"  part2: {sum nums}"

end Part2
end Day01

def day01 (alt : Option String): IO Unit := do
  linesOf 2023 1 alt >>= Day01.Part1.solve >>= Day01.Part2.solve
