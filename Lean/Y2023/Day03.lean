import «AoC».Basic

namespace Y2023.Day03
open Accumulation

def date : AocProblem := AocProblem.new 2023 3

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

def to_numbers (lines : Array String) : List Number :=
  lines.foldl (fun (row, result) line =>
      line |> numbers_in_line |>.map (fun n => Number.new row n.fst n.snd.fst n.snd.snd) |> (row + 1, result ++ .))
    ((0, []) : Int × List Number)
  |>.snd

def Part1.solve (lines : Array String) : Nat :=
  let cands := symbols lines
  let nums  := to_numbers lines
  let part_number := nums.filter
      (fun num => cands.any (fun (y, x) => (num.row - y).natAbs ≤ 1 && num.beg ≤ x && x ≤ num.en))
  part_number.map (·.val) |> sum

def Part2.solve (lines : Array String) : Nat :=
  let cands := asterisks lines
  let nums  := to_numbers lines
  let gears := cands.foldl
    (fun acc (y, x) =>
      let neighbors := nums.filter
        (fun num => (num.row - y).natAbs ≤ 1 && num.beg ≤ x && x ≤ num.en)
      if neighbors.length == 2 then neighbors.map (·.val) |> product |> (acc ++ [·]) else acc)
    ([] : List Nat)
  sum gears

protected def solve (ext : Option String) : IO AocProblem := do
  let lines ← date.getLines ext
  return { date with
    answers := some (
      s!"{Y2023.Day03.Part1.solve lines}",
      s!"{Y2023.Day03.Part2.solve lines}") }

end Y2023.Day03
