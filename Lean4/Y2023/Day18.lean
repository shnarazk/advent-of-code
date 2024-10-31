import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2023.Day18

open Accumulation CiCL
open TwoDimensionalVector64

inductive Direction where | U | D | R | L
deriving BEq

instance : ToString Direction where
  toString
  | .U => "↑"
  | .D => "↓"
  | .R => "→"
  | .L => "←"

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
return area matrix, path grid, index to y position in the original world, and index to x

FIXME: it should also build the map, by another loop on w₁.
-/
def toParityMap (w₁ : Array Input) : (Rect (Option (Direction × (Int × Int)))) :=
  let path : Array ((Int × Int) × Direction) := w₁.foldl
      (fun (l, last) i ↦
        let pos := match i.dir with
        | Direction.D => ((last.fst : Int) + (i.length : Int), last.snd)
        | Direction.U => ((last.fst : Int) - (i.length : Int), last.snd)
        | Direction.R => (last.fst, (last.snd : Int) + (i.length : Int))
        | Direction.L => (last.fst, (last.snd : Int) - (i.length : Int))
        ((pos, i.dir) :: l, pos))
      ([], (0, 0))
    |>.fst
    |>.toArray
  let ys : Array Int := path.map (·.fst.fst) |> unique |>.heapSort (· < ·)
  let xs : Array Int := path.map (·.fst.snd) |> unique |>.heapSort (· < ·)
  path.foldl
      (fun r ((y₁, x₁), dir) ↦
        let y₂ := ys.enumerate.find? (fun iy ↦ iy.snd == y₁) |>.mapOr (·.fst) 0
        let x₂ := xs.enumerate.find? (fun ix ↦ ix.snd == x₁) |>.mapOr (·.fst) 0
        r.set y₂.toUInt64 x₂.toUInt64 (some (dir, ys[y₂]!, xs[x₂]!)))
      (Rect.ofDim2 ys.size.toUInt64 xs.size.toUInt64 none)
-- #eval List.range' 3 (5 - 3)
-- #eval [(5, 8), (3,6), (8, 1), (0, 3)].map (·.fst) |>.mergeSort

-- #eval [(5 : Int), 8, 9].head (by simp)
--- #eval List.zip [0, 1, 3, 4].dropLast [0, 1, 3, 4].tail
#eval List.zip [0, 1, 2, 3, 4] <| List.zip [0, 1, 2, 3, 4].tail.dropLast [0, 1, 2, 3, 4].tail.tail
def scanLine (total last_line_sum : Nat) (last_y : Int) :
    (List (List (Direction × Int × Int))) → Nat
  | [] => total + last_line_sum
  | l :: r' =>
      let y : Int := (l[0]?.mapOr (·.snd.fst) last_y)
      let lastHeight : Nat := (y - last_y).toNat
      let windows3 := List.zip l <| List.zip l.tail.dropLast l.tail.tail
      let line_sum : Int := windows3.map
          (fun (prev, curr, next) ↦ match prev.fst, curr.fst, next.fst with
            | _, .U,  _ | _, .D,  _ => 1
            | _, .L,  _ => prev.snd.snd - curr.snd.snd
            | _, .R,  _ => curr.snd.snd - next.snd.snd)
        |> sum
        |> (· + (l.head?.mapOr (·.snd.snd) 0))
        |> (· + (l.getLast?.mapOr (·.snd.snd) 0))
      scanLine (total + last_line_sum * lastHeight) (dbg "line_sum" line_sum.toNat) y r'

def solve (ai : Array Input) : Nat :=
  let area := toParityMap ai |>.to2Dmatrix |>.map (fun l ↦ l.filterMap I)
  dbg s!"area: {area}" <| scanLine 0 0 0 area

end Part2

def solve := AocProblem.config 2023 18 parser.parse Part1.solve Part2.solve

end Y2023.Day18
