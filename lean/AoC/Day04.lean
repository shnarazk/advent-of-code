import Std
import «AoC».Basic

namespace Day04

def parsed (source : String) : List Nat × List Nat :=
  (toNats targets, toNats cands)
  where
    body := List.getD (String.split source (. == ':')) 1 ""
    parts := String.split body (. == '|')
    targets := List.getD parts 0 "no num"
    cands := List.getD parts 1 "no name"
    toNats := fun (s : String) =>
      let pair := String.split s.trim (. == ' ')
      let numbers := List.filter (fun s => s != "") pair
      List.map String.toNat! numbers

#eval parsed "Card 1: 41 48 | 83  1 41"

def solve1_line (line : String) : Nat :=
  match found.length with
  | 0 => 0
  | n => 2 ^ (n - 1)
  where
    x := parsed line
    found := List.filter (fun c => List.contains x.fst c) x.snd

#eval solve1_line "Card 1: 41 48  2 | 83  1 41 68"
#eval solve1_line "Card 1: 41 48    | 83  1 41 48"
#eval solve1_line "Card 1: 41 48  2 |  2 83  41 48"
#eval solve1_line "Card 1: 41 48  2 |  3 83  42 49"

def solve1 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve1_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part1: {sum}"
  return ()

def solve2_rec (n : Nat) (counts : Array Nat) (table : List (List Nat × List Nat)) : Nat :=
  match table with
  | [] => Array.foldr (. + .) 0 counts
  | List.cons line table' =>
    let found := List.filter (fun c => List.contains line.fst c) line.snd
    let num := counts.get! n
    let counts' := List.foldr (fun k c => c.modify (n + k) (. + num)) counts (List.iota found.length)
    solve2_rec (n+1) counts' table'

def solve2 (lines : Array String) : IO Unit := do
  let table := List.map parsed lines.toList
  let counts := Array.mkArray lines.size 1
  let sum := solve2_rec 0 counts table
  IO.println s!" part2: {sum}"
  return ()

end Day04

def day04 (ext : Option String): IO Unit := do
  let data ← linesOf 2023 4 ext
  pure data >>= Day04.solve1
  pure data >>= Day04.solve2
