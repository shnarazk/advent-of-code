import Std
import «AoC».Basic

namespace Day04

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

def solve1_line (line : String) : Nat :=
  let x     := parsed line
  let found := x.snd.filter (x.fst.contains ·)
  match found.length with
  | 0 => 0
  | n => 2 ^ (n - 1)

-- #eval solve1_line "Card 1: 41 48  2 | 83  1 41 68"
-- #eval solve1_line "Card 1: 41 48    | 83  1 41 48"
-- #eval solve1_line "Card 1: 41 48  2 |  2 83  41 48"
-- #eval solve1_line "Card 1: 41 48  2 |  3 83  42 49"

def Part1.solve (lines : Array String) : IO Unit := do
  let points : Array Nat := lines.map solve1_line
  let sum := points.foldl (. + .) 0
  IO.println s!"  part1: {sum}"

def solve2_rec (n : Nat) (counts : Array Nat) (table : List (List Nat × List Nat)) : Nat :=
  match table with
  | [] => counts.foldr (. + .) 0
  | List.cons line table' =>
    let found   := line.snd.filter (line.fst.contains ·)
    let num     := counts.get! n
    let counts' := (List.iota found.length).foldr (fun k c => c.modify (n + k) (. + num)) counts
    solve2_rec (n+1) counts' table'

def Part2.solve (lines : Array String) : IO Unit := do
  let table  := lines.toList.map parsed
  let counts := Array.mkArray lines.size 1
  let sum    := solve2_rec 0 counts table
  IO.println s!"  part2: {sum}"

end Day04

def day04 (ext : Option String) : IO Unit := do
  let data ← linesOf 2023 4 ext
  Day04.Part1.solve data
  Day04.Part2.solve data
