import Std
import «AoC».Basic

namespace Day02

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

#eval (toHashMap "case 1: 3 red; 5 blue").findEntry? "blue" = some ("blue", 5)

def solve1_line (line : String) : Nat :=
  if   Std.HashMap.findD hash "red" 0   ≤ 12
    && Std.HashMap.findD hash "green" 0 ≤ 13
    && Std.HashMap.findD hash "blue" 0  ≤ 14
  then Std.HashMap.find! hash "«id»"
  else 0
  where
    hash := toHashMap line

def solve1 (lines : Array String) : IO Unit := do
  let points : Array Nat := lines.map solve1_line
  let sum := points.foldl (· + ·) 0
  IO.println s!"  part1: {sum}"

def solve2_line (line : String) : Nat :=
  (Std.HashMap.findD hash "red" 0)
  * (Std.HashMap.findD hash "green" 0)
  * (Std.HashMap.findD hash "blue" 0)
  where
    hash := toHashMap line

def solve2 (lines : Array String) : IO Unit := do
  let points : Array Nat := lines.map solve2_line
  let sum := points.foldl (· + ·) 0
  IO.println s!"  part2: {sum}"

end Day02

def day02 (ext : Option String) : IO Unit := do
  let data ← linesOf 2023 2 ext
  Day02.solve1 data
  Day02.solve2 data
