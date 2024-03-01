import Std
import «AoC».Basic

namespace Day02

def toHashMap (source : String) /- : Std.HashMap String Nat -/ :=
  List.foldl
    (fun hash items =>
      List.foldl
        (fun hash assoc =>
          let (l, n) := association assoc
          hash.insert l n)
        hash
        items
    )
    Std.HashMap.empty
    items_in_bags
  where
    body := List.getD (String.split source (. == ':')) 1 ""
    turns := String.split body (. == ';')
    items_in_bags := turns.map (fun b => String.split b (. == ','))
    association := fun s =>
      let pair := String.split s.trim (. == ' ')
      let value := (List.getD pair 0 "no num").trim.toInt!
      let label := (List.getD pair 1 "no name").trim
      (label, value)

#eval (toHashMap "case 1: 3 red; 5 blue").findEntry? "blue" = some ("blue", 5)

def solve1_line (line : String) : Nat :=
  Std.HashMap.size hash
  where
    hash := toHashMap line

def solve1 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve1_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!" part1: not yet implemented {lines.size}, {sum}"
  return ()

def solve2 (lines : Array String) : IO Unit := do
  IO.println s!" part2: not yet implemented {lines.size}"
  return ()

end Day02

def day02 : IO Unit := do
  let data ← dataFor 2023 2
  pure data >>= Day02.solve1
  pure data >>= Day02.solve2
