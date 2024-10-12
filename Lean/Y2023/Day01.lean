import «AoC».Basic

namespace Y2023.Day01
open Accumulation

def date : AocProblem := AocProblem.new 2023 1

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

def solve (lines : Array String) : Nat :=
  lines.map (fun s =>
      (List.takeWhile (. != []) s.toList.tails).map mnemonic |> Part1.evaluate)
    |> sum

end Part2

protected def solve (alt : Option String): IO AocProblem:= do
  let lines ← date.getLines alt
  return { date with
    input_name := (← date.fileName alt)
    answers := some (
      s!"{Part1.solve lines}",
      s!"{Part2.solve lines}") }

end Y2023.Day01
