import «AoC».Basic

namespace Y2023.Day04

open Accumulation

def parsed (source : String) : List Nat × List Nat :=
  (toNats targets, toNats cands)
  where
    body    := (String.split source (. == ':')).getD 1 ""
    parts   := body.split (. == '|')
    targets := parts.getD 0 "no num"
    cands   := parts.getD 1 "no name"
    toNats  := fun (s : String) =>
      let pair := String.split s.trim (. == ' ')
      let numbers := pair.filter (fun s => s != "")
      numbers.map String.toNat!

-- #eval parsed "Card 1: 41 48 | 83  1 41"

namespace Part1

def evaluate (line : String) : Nat :=
  let x     := parsed line
  let found := x.snd.filter (x.fst.contains ·)
  match found.length with
  | 0 => 0
  | n => 2 ^ (n - 1)

-- #eval evaluate "Card 1: 41 48  2 | 83  1 41 68"
-- #eval evaluate "Card 1: 41 48    | 83  1 41 48"
-- #eval evaluate "Card 1: 41 48  2 |  2 83  41 48"
-- #eval evaluate "Card 1: 41 48  2 |  3 83  42 49"

def solve (lines : Array String) : Nat := sum $ lines.map evaluate

end Part1

namespace Part2
def evaluate (n : Nat) (counts : Array Nat) (table : List (List Nat × List Nat)) : Nat :=
  match table with
  | [] => counts.foldr (. + .) 0
  | List.cons line table' =>
    let found   := line.snd.filter (line.fst.contains ·)
    let num     := counts.get! n
    let counts' := (List.iota found.length).foldr (fun k c => c.modify (n + k) (. + num)) counts
    evaluate (n + 1) counts' table'

def solve (lines : Array String) : Nat :=
  evaluate 0 (Array.mkArray lines.size 1) (lines.toList.map parsed)

end Part2

def solve := AocProblem.config 2023 4
  (·.splitOn "\n" |>.dropLast |>.toArray |> some) Part1.solve Part2.solve

end Y2023.Day04
