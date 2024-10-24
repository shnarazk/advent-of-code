import «AoC».Basic

namespace Y2023.Day02

open Accumulation

def toHashMap (source : String) : Std.HashMap String Nat :=
  List.foldl
    (fun hash items =>
      List.foldl
        (fun hash assoc =>
          let (l, n) := association assoc
          match hash.get? l with
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
  if hash.getD "red" 0 ≤ 12 && hash.getD "green" 0 ≤ 13 && hash.getD "blue" 0 ≤ 14
  then hash.get! "«id»"
  else 0

def solve (lines : Array String) : Nat := lines.map evaluate |> sum

end Part1

namespace Part2

def evaluate (line : String) : Nat :=
  let hash := toHashMap line
  (hash.getD "red" 0) * (hash.getD "green" 0) * (hash.getD "blue" 0)

def solve (lines : Array String) : Nat := lines.map evaluate |> sum

end Part2

def solve := AocProblem.config 2023 2
  (·.splitOn "\n" |>.dropLast |>.toArray |>some) Part1.solve Part2.solve

end Y2023.Day02
