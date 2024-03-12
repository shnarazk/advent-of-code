import Std
import «AoC».Basic

namespace Day02
open Accumulation

def toHashMap (source : String) : Std.HashMap String Nat :=
  List.foldl
    (fun hash items =>
      List.foldl
        (fun hash assoc =>
          let (l, n) := association assoc
          match hash.find? l with
          | some n' => hash.insert l $ max n n'
          | none    => hash.insert l n)
        hash
        items
    )
    (Std.HashMap.empty.insert "«id»" id)
    items_in_bags
  where
    id := ((List.getD (source.split (. == ':')) 0 "-1").drop 5).trim.toNat!
    body := List.getD (source.split (. == ':')) 1 ""
    turns := body.split (. == ';')
    items_in_bags := turns.map (fun b => b.split (. == ','))
    association := fun s =>
      let pair := String.split s.trim (· == ' ')
      let value := (pair.getD 0 "no num").trim.toNat!
      let label := (pair.getD 1 "no name").trim
      (label, value)

namespace Part1

def evaluate (line : String) : Nat :=
  let hash := toHashMap line
  if hash.findD "red" 0 ≤ 12 && hash.findD "green" 0 ≤ 13 && hash.findD "blue" 0 ≤ 14
  then hash.find! "«id»"
  else 0

def solve (lines : Array String) : IO (Array String) := do
  IO.println s!"  part1: {lines.map evaluate |> sum}"
  return lines

end Part1

namespace Part2

def evaluate (line : String) : Nat :=
  let hash := toHashMap line
  (hash.findD "red" 0) * (hash.findD "green" 0) * (hash.findD "blue" 0)

def solve (lines : Array String) : IO Unit := do
  IO.println s!"  part2: {lines.map evaluate |> sum}"

end Part2

end Day02

def day02 (ext : Option String) : IO Unit := do
  linesOf 2023 2 ext >>= Day02.Part1.solve >>= Day02.Part2.solve
