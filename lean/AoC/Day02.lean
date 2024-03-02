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
          | some n' => hash.insert l (max n n')
          | none => hash.insert l n)
        hash
        items
    )
    (Std.HashMap.empty.insert "«id»" id)
    items_in_bags
  where
    id := ((List.getD (String.split source (. == ':')) 0 "-1").drop 5).trim.toNat!
    body := List.getD (String.split source (. == ':')) 1 ""
    turns := String.split body (. == ';')
    items_in_bags := turns.map (fun b => String.split b (. == ','))
    association := fun s =>
      let pair := String.split s.trim (· == ' ')
      let value := (List.getD pair 0 "no num").trim.toNat!
      let label := (List.getD pair 1 "no name").trim
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
  let points : Array Nat := Array.map solve1_line lines
  let sum := Array.foldl (· + ·) 0 points
  IO.println s!" part1: {sum}"
  return ()

def solve2_line (line : String) : Nat :=
  (Std.HashMap.findD hash "red" 0)
  * (Std.HashMap.findD hash "green" 0)
  * (Std.HashMap.findD hash "blue" 0)
  where
    hash := toHashMap line

def solve2 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  let sum := Array.foldl (· + ·) 0 points
  IO.println s!" part1: {sum}"
  return ()

end Day02

def day02 (ext : Option String) : IO Unit := do
  let data ← linesOf 2023 2 ext
  pure data >>= Day02.solve1
  pure data >>= Day02.solve2
