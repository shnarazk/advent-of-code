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
  if accum'.get (i, j) true then return (accum', 0)
  let some ch := grid.get? (i, j) | return (accum', 0)
  let mut accum := accum'
  let mut count := 0
  let mut checked : Rect Bool := accum.map (K false)
  if checked.geometory != grid.geometory then return (accum, dbg "!!!" 0)
  let mut to_visit := [(i, j)]
  let mut seg_h : HashSet Vec₂ := HashSet.emptyWithCapacity 100
  let mut seg_v : HashSet Vec₂ := HashSet.emptyWithCapacity 100
  while !to_visit.isEmpty do
    let p :: to_visit' := to_visit | continue
    to_visit := to_visit'
    if checked.get p true then continue
    checked := checked.set p true
    if grid.get? p == some ch then
      count := count + 1
      accum := accum.set p true
      if p.fst == 0 || grid.get? (p.fst - 1, p.snd) != some ch then seg_h := seg_h.insert p
      if               grid.get? (p.fst + 1, p.snd) != some ch then seg_h := seg_h.insert (p.fst + 1, p.snd)
      if p.snd == 0 || grid.get? (p.fst, p.snd - 1) != some ch then seg_v := seg_v.insert p
      if               grid.get? (p.fst, p.snd + 1) != some ch then seg_v := seg_v.insert (p.fst, p.snd + 1)
      for dir in [Dir.N, Dir.E, Dir.S, Dir.W] do
        let some q := p + dir | continue
        if grid.validIndex? q then to_visit := to_visit.concat q
  (accum, count * (seg_v.size + seg_h.size))

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

instance : Ord (Nat × Bool) where
  compare a b := match compare a.fst b.fst with
  | Ordering.eq => compare a.snd b.snd
  | cmp => cmp

def count_sides (hash : HashMap Nat (Array (Nat × Bool))) : Nat :=
  hash.values.iter
    |>.map (fun v' ↦ Id.run do
      let v := v'.qsortOrd
      let mut count := 1
      let mut ended := v[0]!.fst + 1
      let mut spin := v[0]!.snd
      for (st, sp) in v.drop 1 |>.iter do
        if ended != st || spin != sp then count := count + 1
        ended := st + 1
        spin := sp
      count)
    |>.sum

def evaluate_at (accum' : Rect Bool) (grid : Rect Char) (i j : Nat) : Rect Bool × Nat := Id.run do
  if accum'.get (i, j) true then return (accum', 0)
  let some ch := grid.get? (i, j) | return (accum', 0)
  let mut accum := accum'
  let mut count := 0
  let mut checked : Rect Bool := accum.map (K false)
  if checked.geometory != grid.geometory then return (accum, dbg "!!!" 0)
  let mut to_visit := [(i, j)]
  let mut seg_h : HashSet ((Nat × Nat) × Bool) := HashSet.emptyWithCapacity 100
  let mut seg_v : HashSet ((Nat × Nat) × Bool) := HashSet.emptyWithCapacity 100
  while !to_visit.isEmpty do
    let p :: to_visit' := to_visit | continue
    to_visit := to_visit'
    if checked.get p true then continue
    checked := checked.set p true
    if grid.get? p == some ch then
      count := count + 1
      accum := accum.set p true
      if p.fst == 0 || grid.get? (p.fst - 1, p.snd) != some ch then seg_h := seg_h.insert (p, false)
      if grid.get? (p.fst + 1, p.snd) != some ch then seg_h := seg_h.insert ((p.fst + 1, p.snd), true)
      if p.snd == 0 || grid.get? (p.fst, p.snd - 1) != some ch then seg_v := seg_v.insert (p, false)
      if grid.get? (p.fst, p.snd + 1) != some ch then seg_v := seg_v.insert ((p.fst, p.snd + 1), true)
      for dir in [Dir.N, Dir.E, Dir.S, Dir.W] do
        let some q := p + dir | continue
        if grid.validIndex? q then to_visit := to_visit.concat q
  -- build longer segments
  let hss : HashMap Nat (Array (Nat × Bool)) := seg_h.iter
    |>.fold
      (fun (acc : HashMap Nat (Array (Nat × Bool))) ps ↦
        let (pos, spin) := ps
        acc.alter pos.fst (fun ol ↦ some <| (ol.unwrapOr #[]).push (pos.snd, spin)))
      (HashMap.emptyWithCapacity 100)
  let vss : HashMap Nat (Array (Nat × Bool)) := seg_v.iter
    |>.fold
      (fun (acc : HashMap Nat (Array (Nat × Bool))) ps ↦
        let (pos, spin) := ps
        acc.alter pos.snd (fun ol ↦ some <| (ol.unwrapOr #[]).push (pos.fst, spin)))
      (HashMap.emptyWithCapacity 100)
  (accum, count * (count_sides hss + count_sides vss))

def solve (input : Input) : Nat := Id.run do
  let mut accum := input.grid.map (K false)
  let mut sum := 0
  for h in 0 ... input.grid.height do
    for w in 0 ... input.grid.width do
      let (accum', c) := evaluate_at accum input.grid h w
      accum := accum'
      sum := sum + c
  return sum

end Part2

public def solve := AocProblem.config 2024 12 parser.parse Part1.solve Part2.solve

end Y2024.Day12
