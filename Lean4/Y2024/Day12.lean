module

public import Itertools
public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec

namespace Y2024.Day12

open Std Dim2 CiCL

structure Input where
  grid : Rect Char
deriving BEq

instance : ToString Input where toString s := s!"{s.grid}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let grid ← separated alphabets eol
      return Input.mk (Rect.of2DMatrix (grid.map (·.toList.toArray)))

end parser

namespace Part1

def evaluate_at (accum' : Rect Bool) (grid : Rect Char) (i j : Nat) : Rect Bool × Nat := Id.run do
  if accum'.get (i, j) false then return (accum', 0)
  let some c := grid.get? (i, j) | return (accum', 0)
  let mut accum := accum'
  let mut count := 0
  let mut r : Rect (Option Bool) := accum.map (K none)
  let mut to_visit := [(i, j)]
  let mut seg_h : HashSet Vec₂ := HashSet.emptyWithCapacity 100
  let mut seg_v : HashSet Vec₂ := HashSet.emptyWithCapacity 100
  while !to_visit.isEmpty do
    let p :: to_visit' := to_visit | continue
    to_visit := to_visit'
    to_visit := to_visit.drop 1
    if some none != r.get? p then continue
    if grid.get? p == some c then
      count := count + 1
      accum := accum.set p true
      r := r.set p (some true)
      if grid.get? (p.fst - 1, p.snd) != some c then seg_h := seg_h.insert p
      if grid.get? (p.fst + 1, p.snd) != some c then seg_h := seg_h.insert (p.fst + 1, p.snd)
      if grid.get? (p.fst, p.snd - 1) != some c then seg_v := seg_v.insert p
      if grid.get? (p.fst, p.snd + 1) != some c then seg_v := seg_v.insert (p.fst, p.snd + 1)
      -- TODO: neighbors
    else
      r := r.set p (some false)
  (accum, i * j)

def solve (input : Input) : Nat := Id.run do
  let mut accum := input.grid.map (K false)
  let mut sum := 0
  for h in 0 ... input.grid.height do
    for w in 0 ... input.grid.width do
      let (accum', c) := evaluate_at accum input.grid h w
      accum := accum'
      sum := sum + c
  return sum

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2024 12 parser.parse Part1.solve Part2.solve

end Y2024.Day12
