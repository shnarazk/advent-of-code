import «AoC».Basic
import Batteries.Data.List.Basic

namespace Y2023.Day01
open Accumulation

namespace Part1

def evaluate (s : List Char) : Nat :=
  let asNum (c : Char) : Nat := c.toNat - '0'.toNat
  let sk := s.filter Char.isDigit
  asNum sk.head! * 10 + asNum sk.getLast!

def solve (lines : Array String) : Nat :=
  sum $ lines.map (fun (s) => evaluate s.toList)

end Part1

namespace Part2

def mnemonic (s : List Char) : Char :=
  if        "one".toList.isPrefixOf s then '1'
  else if   "two".toList.isPrefixOf s then '2'
  else if "three".toList.isPrefixOf s then '3'
  else if  "four".toList.isPrefixOf s then '4'
  else if  "five".toList.isPrefixOf s then '5'
  else if   "six".toList.isPrefixOf s then '6'
  else if "seven".toList.isPrefixOf s then '7'
  else if "eight".toList.isPrefixOf s then '8'
  else if  "nine".toList.isPrefixOf s then '9'
  else s[0]!

def solve (lines : Array String) : Nat :=
  lines.map (fun s =>
      (List.takeWhile (. != []) s.toList.tails).map mnemonic |> Part1.evaluate)
    |> sum

end Part2

def solve := AocProblem.config 2023 1
  (·.splitOn "\n" |>.dropLast |>.toArray |>some) Part1.solve Part2.solve

end Y2023.Day01
