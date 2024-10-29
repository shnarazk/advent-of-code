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
        if h : 2 = b.length then
          have H1 : 1 < b.length := by simp [←h]
          have H0 : 0 < b.length := by exact Nat.zero_lt_of_lt H1
          if 1 < b[1]'H1 - b[0]'H0 then some (y, (b[1] + b[0]) / 2) else none
        else
          none)
  dbg s!"{cands}" cands[0]!

def solve (l : Array Input) : Nat :=
  let heightₚ := l.filter (·.dir == .D) |>.map (·.length) |> sum
  let heightₘ := l.filter (·.dir == .U) |>.map (·.length) |> sum
  let widthₚ  := l.filter (·.dir == .R) |>.map (·.length) |> sum
  let widthₘ  := l.filter (·.dir == .L) |>.map (·.length) |> sum
  let width := widthₚ.max  widthₘ |>(· + 1)
  let height := heightₚ.max heightₘ |>(· + 1)
  let r := l.foldl
      (fun (pos, r) input ↦
        (List.range input.length).foldl
          (fun (pos, r) _ ↦
          let p := match input.dir with
            | .U => (pos.fst - 1, pos.snd)
            | .R => (pos.fst, pos.snd + 1)
            | .D => (pos.fst + 1, pos.snd)
            | .L => (pos.fst, pos.snd - 1)
          (p, r.set p.fst p.snd 1))
          (pos, r)
      )
      ((0, 0), Rect.ofDim2 height.toUInt64 width.toUInt64 0)
    |>.snd
  dbg s!"h: {height}, w: {width}: {r}" <| find_inner_point r
    |>(fun p ↦ p.fst + p.snd)

end Part1

namespace Part2

def solve (_ : Array Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 18 parser.parse Part1.solve Part2.solve

end Y2023.Day18
