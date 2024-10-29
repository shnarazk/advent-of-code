import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2023.Day18

open Accumulation CiCL
open TwoDimensionalVector64

inductive Direction where | U | D | R | L
deriving BEq

structure Input where
  dir : Direction
  length : Nat
  colorCode : Nat
deriving BEq

instance : ToString Input where toString s := s!"{s.colorCode}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

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
  return (Input.mk
      dist
      num
      (hexs.map
          (fun c ↦ ("0123456789abcdef".enumerate.find? (Prod.snd · == c)).mapOr (·.fst) 0)
        |>.foldl (fun (acc v : Nat) ↦ acc * 16 + v) 0))

def parse : String → Option (Array Input) := AoCParser.parse parser
  where
    parser : Parser (Array Input) := sepBy1 line eol

end parser

namespace Part1

def find_inner_point (r : Rect Nat) : Nat × Nat :=
  let height := r.height
  let width := r.width
  let cands := List.range height.toNat
      |>.filterMap (fun y ↦
        let b := List.range width.toNat
            |>.filter (fun x ↦ r.get y.toUInt64 x.toUInt64 0 == 1)
        if h : b.length = 2 then
          have H1 : 1 < b.length := by simp [h]
          have H0 : 0 < b.length := by simp [h]
          if 1 < b[1]'H1 - b[0]'H0 then some (y, (b[1] + b[0]) / 2) else none
        else
          none)
  dbg s!"{cands}" cands[0]!

-- #eval true.map (K (3 : Nat))

partial def fill (r : Rect Nat) (to_visit : List (Nat × Nat)) : Rect Nat :=
  match to_visit with
  | [] => r
  | pos :: to_visit' =>
    let h := (r.height - 1).toNat
    let w := (r.width - 1).toNat
    match r.get pos.fst.toUInt64 pos.snd.toUInt64 1 with
    | 0 =>
      let r' := r.set pos.fst.toUInt64 pos.snd.toUInt64 1
      let to_u := (0 < pos.fst : Bool).map (K (pos.fst - 1, pos.snd))
      let to_d := (pos.fst < h : Bool).map (K (pos.fst + 1, pos.snd))
      let to_l := (0 < pos.snd : Bool).map (K (pos.fst, pos.snd - 1))
      let to_r := (pos.snd < w : Bool).map (K (pos.fst, pos.snd + 1))
      let nexts := [to_u, to_d, to_l, to_r].filterMap I
        |>.filter (fun p ↦ r'.get p.fst.toUInt64 p.snd.toUInt64 1 = 0)
      fill r' (nexts ++ to_visit')
    | _ =>
      fill r to_visit'

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
          (p, r.set (p.fst + offset_h).toUInt64 (p.snd + offset_w).toUInt64 1))
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

/-
Convert a world to the compact one.
return area matrix, index to y position in the original world, and index to x
-/
def toCompact (w₁ : Array Input) : (Rect Nat) × (Array Nat) × (Array Nat) :=
  let ys : Array Nat := w₁.foldl (fun l i ↦
      match l with
        | last :: _ => match i.dir with
          | Direction.D => (last.fst + i.length, true) :: l
          | Direction.U => (last.fst - i.length, false) :: l
          | _ => l
        | [] => [])
      [(0, false)]
    |>.toArray
    |>.map (fun (n, b) ↦ if b then n + 1 else n)
    |> unique
    |>.heapSort (· < ·)
  let xs : Array Nat := w₁.foldl (fun l i ↦
      match l with
        | last :: _ => match i.dir with
          | Direction.R => (last.fst + i.length, true) :: l
          | Direction.L => (last.fst - i.length, false) :: l
          | _ => l
        | [] => [])
      [(0, false)]
    |>.toArray
    |>.map (fun (n, b) ↦ if b then n + 1 else n)
    |> unique
    |>.heapSort (· < ·)

  let h₂ := ys.size
  let w₂ := xs.size

  let r₂ := Rect.ofDim2 h₂.toUInt64 w₂.toUInt64 1
  (r₂, ys, xs)

-- #eval [(5, 8), (3,6), (8, 1), (0, 3)].map (·.fst) |>.mergeSort

def solve (_a : Array Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 18 parser.parse Part1.solve Part2.solve

end Y2023.Day18
