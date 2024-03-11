import Std
import «AoC».Basic

namespace Day03
open Accumulation

structure Number where
  new ::
  row : Int
  beg : Int
  en  : Int
  val : Nat
deriving Ord, Repr

instance : ToString Number where
  toString n := String.join [toString n.val, toString (n.row, n.beg, n.en)]

def symbols (lines : Array String) : List (Int × Int) :=
  lines.foldl (fun (i, l) line =>
      (i + 1, line.foldl (fun (j, l) ch =>
          (j + 1, if !ch.isDigit &&  ch != '.' then l ++ [(i, j)] else l))
        (0, l)
      |>.snd))
    ((0, []) : Int × List (Int × Int))
  |>.snd

def asterisks (lines : Array String) : List (Int × Int) :=
  lines.foldl (fun (i, l) line =>
      (i + 1, line.foldl (fun (j, l) ch =>
          (j + 1, if ch == '*' then l ++ [(i, j)] else l))
        (0, l)
      |>.snd))
    ((0, []) : Int × List (Int × Int))
  |>.snd

def numbers_in_line (line : String) : List (Int × Int × Nat) :=
  (line ++ ".").foldl
    (fun (result, index, tmp) ch =>
      match ch.isDigit, tmp with
      | true, none => (result, index + 1, some (index-1, ch.toNat - '0'.toNat))
      | true, some (s, v) => (result, index + 1, some (s, v * 10 + ch.toNat - '0'.toNat))
      | false, some (s, v) => (result++[(s, index, v)], index + 1, none)
      | _, _ => (result, index + 1, tmp)
    )
    (([] : List (Int × Int × Nat)), 0, (none : Option (Int × Nat)))
  |>.fst

#eval numbers_in_line "467..114.."

def numbers (lines : Array String) : List Number :=
  lines.foldl (fun (row, result) line =>
      line |> numbers_in_line |>.map (fun n => Number.new row n.fst n.snd.fst n.snd.snd) |> (row + 1, result ++ .))
    ((0, []) : Int × List Number)
  |>.snd

#eval (3 : Int).natAbs

def solve1 (lines : Array String) : IO Unit := do
  let cands := symbols lines
  let numbers := numbers lines
  let part_number := numbers.filter
        (fun num => cands.any (fun (y, x) => (num.row - y).natAbs ≤ 1 && num.beg ≤ x && x ≤ num.en))
  IO.println s!"  part1: {part_number.map (·.val) |> sum}"

def solve2 (lines : Array String) : IO Unit := do
  let cands := asterisks lines
  let numbers := numbers lines
  let gears := cands.foldl
    (fun acc (y₀, x₀) =>
      let neighbors := numbers.filter (fun num => (num.row - y₀).natAbs ≤ 1 && num.beg ≤ x₀ && x₀ ≤ num.en)
      if neighbors.length == 2 then (neighbors.map (·.val) |>.foldl (fun a x => a * x) 1 |> (acc ++ [·])) else acc)
    ([] : List Nat)
  IO.println s!"  part2: {sum gears}"

end Day03

def day03 (ext : Option String) : IO Unit := do
  let data ← linesOf 2023 3 ext
  Day03.solve1 data
  Day03.solve2 data
