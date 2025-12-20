module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Rect64

namespace Y2023.Day18

open Accumulation CiCL
open TwoDimensionalVector64

inductive Direction where | U | D | R | L deriving BEq

instance : ToString Direction where
  toString
  | .U => "↑"
  | .D => "↓"
  | .R => "→"
  | .L => "←"

structure Input where
  dir : Direction
  length : Nat
  colorCode : Direction × Nat
deriving BEq

instance : ToString Input where toString s := s!"{s.colorCode}"

def find_inner_point (r : Rect Nat) : Nat × Nat :=
  let height := r.height
  let width := r.width
  let cands := List.range height.toNat
      |>.filterMap (fun y ↦
        let b := List.range width.toNat
            |>.filter (fun x ↦ r.get (y.toUInt64, x.toUInt64) 0 == 1)
        if h : b.length = 2 then
          have H1 : 1 < b.length := by simp [h]
          have H0 : 0 < b.length := by simp [h]
          if 1 < b[1]'H1 - b[0]'H0 then some (y, (b[1] + b[0]) / 2) else none
        else
          none)
  cands[0]!

partial
def fill (r : Rect Nat) (to_visit : List (Nat × Nat)) : Rect Nat :=
  match to_visit with
  | [] => r
  | pos :: to_visit' =>
    let h := (r.height - 1).toNat
    let w := (r.width - 1).toNat
    match r.get (pos.fst.toUInt64, pos.snd.toUInt64) 1 with
    | 0 =>
      let r' := r.set (pos.fst.toUInt64, pos.snd.toUInt64) 1
      let to_u := (0 < pos.fst : Bool).map (K (pos.fst - 1, pos.snd))
      let to_d := (pos.fst < h : Bool).map (K (pos.fst + 1, pos.snd))
      let to_l := (0 < pos.snd : Bool).map (K (pos.fst, pos.snd - 1))
      let to_r := (pos.snd < w : Bool).map (K (pos.fst, pos.snd + 1))
      let nexts := [to_u, to_d, to_l, to_r].filterMap I
        |>.filter (fun p ↦ r'.get (p.fst.toUInt64, p.snd.toUInt64) 1 = 0)
      fill r' (nexts ++ to_visit')
    | _ =>
      fill r to_visit'

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def decode_hex (str : Array Char) : Direction × Nat :=
  let (hex, dir) := str.toList.splitAt 5
  (match dir.head? with
      | some '0' => Direction.R
      | some '1' => Direction.D
      | some '2' => Direction.L
      | some '3' => Direction.U
      | _ => dbg "Parse error" Direction.U,
    hex.map
        (fun c ↦ ("0123456789abcdef".enum.find? (Prod.snd · == c)).mapOr (·.fst) 0)
      |>.foldl (fun (acc v : Nat) ↦ acc * 16 + v) 0)

example : decode_hex "70c710".toList.toArray = (Direction.R, 461937) := by rfl

def line := do
  let dist ← (
          (pchar 'U' *> return Direction.U)
      <|> (pchar 'D' *> return Direction.D)
      <|> (pchar 'L' *> return Direction.L)
      <|> (pchar 'R' *> return Direction.R))
    <* whitespaces
  let num ← number <* pstring " (#"
  let hexs ← many1 (satisfy (fun c ↦ ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')))
  let _ ← pchar ')'
  return Input.mk dist num (decode_hex hexs)

def parse : String → Option (Array Input) := AoCParser.parse parser
  where
    parser : Parser (Array Input) := separated line eol

end parser

namespace Part1

-- #eval true.map (K (3 : Nat))

def solve (l : Array Input) : Nat :=
  -- shift axis to escape negative index
  let heightₚ := l.filter (·.dir == .D) |>.map (·.length) |> sum
  let heightₘ := l.filter (·.dir == .U) |>.map (·.length) |> sum
  let widthₚ  := l.filter (·.dir == .R) |>.map (·.length) |> sum
  let widthₘ  := l.filter (·.dir == .L) |>.map (·.length) |> sum
  let height := heightₚ + heightₘ |>(· + 1)
  let offset_h := height / 4
  let width := widthₚ + widthₘ |>(· + 1)
  let offset_w := width / 4
  let r := l.foldl
      (fun (pos, r) input ↦
        (List.range input.length).foldl
          (fun (pos, r) _ ↦
          let p := match input.dir with
            | .U => (pos.fst - 1, pos.snd)
            | .R => (pos.fst, pos.snd + 1)
            | .D => (pos.fst + 1, pos.snd)
            | .L => (pos.fst, pos.snd - 1)
          (p, r.set ((p.fst + offset_h).toUInt64, (p.snd + offset_w).toUInt64) 1))
          (pos, r)
      )
      ((offset_h, offset_w), Rect.ofDim2 (height + offset_h).toUInt64 (width + offset_w).toUInt64 0)
    |>.snd
  let start := find_inner_point r
  let r' := fill r [start]
  r'.vector.filter (· == 1) |>.size

end Part1

namespace Part2

abbrev HashMap := Std.HashMap

def fromTo' (b e : Nat) : List Nat :=
  let b' := b.min e
  let e' := b.max e
  List.range' b' (e' - b' + 1)

/-
Convert a world to a uniform compact one.
return area matrix, index to y position in the original world, and index to x
-/
def transform (w₁ : Array Input) : Rect Nat × Array Int × Array Int :=
  let path : Array (Int × Int) := w₁.foldl
      (fun (l, now) i ↦
        let next := match i.dir with
        | Direction.D => ((now.fst : Int) + (i.length : Int), now.snd)
        | Direction.U => ((now.fst : Int) - (i.length : Int), now.snd)
        | Direction.R => (now.fst, (now.snd : Int) + (i.length : Int))
        | Direction.L => (now.fst, (now.snd : Int) - (i.length : Int))
        (now  :: l, next))
      ([], (0, 0))
    |>.fst
    |> ((0,0) :: ·)
    |>.toArray
    |>.reverse
  let ys : Array Int := path.map (·.fst) |> unique |>.heapSort (· < ·)
  let xs : Array Int := path.map (·.snd) |> unique |>.heapSort (· < ·)
  -- doubled map
  let dm := path.windows2.foldl
    (fun r ((y₁, x₁), (y₂, x₂)) ↦
      let y₁' : Nat := ys.enum.find? (fun iy ↦ iy.snd == y₁) |>.mapOr (·.fst) 0
      let x₁' : Nat := xs.enum.find? (fun ix ↦ ix.snd == x₁) |>.mapOr (·.fst) 0
      let y₂' : Nat := ys.enum.find? (fun iy ↦ iy.snd == y₂) |>.mapOr (·.fst) 0
      let x₂' : Nat := xs.enum.find? (fun ix ↦ ix.snd == x₂) |>.mapOr (·.fst) 0
      if y₁' == y₂' then
        fromTo' (2 * x₁') (2 * x₂')
          |>.foldl (fun r x ↦ r.set (2 * y₁'.toUInt64, x.toUInt64) 1) r
      else
        fromTo' (2 * y₁') (2 * y₂')
          |>.foldl (fun r y ↦ r.set (y.toUInt64, 2 * x₁'.toUInt64) 1) r)
    (Rect.ofDim2 (2 * ys.size.toUInt64 + 2) (2 * xs.size.toUInt64 + 2) 0)
  (dm, ys, xs)
-- #eval List.range' 3 (5 - 3)
-- #eval [(5, 8), (3,6), (8, 1), (0, 3)].map (·.fst) |>.mergeSort

-- #eval [(5 : Int), 8, 9].head (by simp)
--- #eval List.zip [0, 1, 3, 4].dropLast [0, 1, 3, 4].tail
-- #eval List.zip [0, 1, 2, 3, 4] <| List.zip [0, 1, 2, 3, 4].tail.dropLast [0, 1, 2, 3, 4].tail.tail
def scanLine (total last_line_sum : Nat) (last_y : Int) :
    (List (List (Direction × Int × Int))) → Nat
  | [] => total + last_line_sum
  | l :: r' =>
      let y : Int := (l[0]?.mapOr (·.snd.fst) last_y)
      let line_total := l.foldl
          (fun (total, beg) (dir, _, x) ↦ match beg, dir with
            | some (start, _), Direction.R => (total, some (start, x))
            | some (start, _), Direction.L => (total, some (start, x))
            | some (start, _), Direction.U => (total + (x - start).toNat + 1, none)
            | some (start, _), Direction.D => (total + (x - start).toNat + 1, none)
            | none, Direction.L => (total, some (x, x))
            | none, Direction.R => (total, some (x, x))
            | none, Direction.U => (total, some (x, x))
            | none, Direction.D => (total, some (x, x)))
          ((0 : Nat), (none : Option (Int × Int)))
        |> (fun (total, beg) ↦ if let some (b, e) := beg then total + (e - b + 1).toNat else total)
      let lastHeight : Nat := (y - last_y).toNat
      let windows2 := List.zip l.dropLast l.tail
      let _line_sum : Int := windows2.map (fun (prev, curr) ↦ curr.snd.snd - prev.snd.snd + 1)
        |>.enumerate
        |>.filter (fun p ↦ p.fst % 2 == 0)
        |>.map (·.snd)
        |> sum
      scanLine (total + last_line_sum * lastHeight) line_total y r'

def solve (path' : Array Input) : Nat :=
  let path := path'.map (fun p ↦ Input.mk p.colorCode.fst p.colorCode.snd p.colorCode)
  let (area, ys, xs) := transform path
  let filled := fill area [find_inner_point area]
  -- convert units
  let width := filled.width / 2
  let height := filled.height / 2
  let total := List.range height.toNat
    |>.foldl (fun acc y ↦
        List.range width.toNat
            |>.foldl
              (fun acc x ↦
                if filled.get? ((2 * y).toUInt64, (2 * x).toUInt64) == some 1 then
                  let area := match
                      filled.get? ((2 * y + 1).toUInt64, (2 * x).toUInt64) == some 1,
                      filled.get? ((2 * y).toUInt64, (2 * x + 1).toUInt64) == some 1,
                      filled.get? ((2 * y + 1).toUInt64, (2 * x + 1).toUInt64) == some 1 with
                    | true,  true,  true  => (ys[y + 1]! - ys[y]!) * (xs[x + 1]! - xs[x]!)
                    | true,  true,  false => (ys[y + 1]! - ys[y]!) + (xs[x + 1]! - xs[x]!) - 1
                    | true,  false, false => ys[y + 1]! - ys[y]!
                    | false, true,  false => xs[x + 1]! - xs[x]!
                    | false, false, false => 1
                    | _, _, _ => dbg "impossible" 0
                  acc + area.toNat
                else
                  acc)
              acc)
      0
  -- dbg s!"ys: {ys}, xs: {xs}\nfilled: {filled}" total
  total

end Part2

public def solve := AocProblem.config 2023 18 parser.parse Part1.solve Part2.solve

end Y2023.Day18
