module

public import Std.Data.Iterators
public import Itertools
public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec

namespace Y2024.Day12

open Std Dim2 CiCL

structure RectHash (t : Type) where
  hashmap :Std.HashMap Int t
  height: Int
  width: Int
deriving BEq, Repr

def RectHash.new (t : Type) (h w : Int) : RectHash t :=
  RectHash.mk Std.HashMap.emptyWithCapacity h w

instance RectHash.isGetElem (t : Type) :
    GetElem? (RectHash t) Vec₂ t (fun h i ↦ i.fst * h.width + i.snd ∈ h.hashmap) where
  getElem? self i := self.hashmap[i.fst * self.width + i.snd]?
  getElem self i p := self.hashmap.get (i.fst * self.width + i.snd) p

@[inline]
def RectHash.set {t : Type} (self : @&RectHash t) (i : Vec₂) (k : t) : RectHash t :=
  { self with hashmap := self.hashmap.insert (i.fst * self.width + i.snd) k }

@[inline]
def RectHash.erase {t : Type} (self : @&RectHash t) (i : Vec₂) : RectHash t :=
  { self with hashmap := self.hashmap.erase (i.fst * self.width + i.snd) }

def RectHash.of2DArray {t : Type} (a : Array (Array t)) : RectHash t := Id.run do
  let mut h := RectHash.new t a.size (a.iter.map (·.size) |>.sum)
  for (i, l) in a.iter.enumerate do
    for (j, v) in l.iter.enumerate do
      h := h.set (i, j) v
  h

structure Input where
  grid : Rect Char
deriving BEq

instance : ToString Input where toString s := s!"{s.grid}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option (RectHash Char) := AoCParser.parse parser
  where
    parser : Parser (RectHash Char) := do
      let grid ← separated alphabets eol
      return RectHash.of2DArray (grid.map (·.toList.toArray))

end parser

namespace Part1

def evaluate_at (accum' : RectHash Bool) (grid : RectHash Char) (i j : Int) : RectHash Bool × Nat := Id.run do
  if accum'[(i, j)]? == some true then return (accum', 0)
  let some ch := grid[(i, j)]? | return (accum', 0)
  let mut accum := accum'
  let mut count := 0
  let mut checked : RectHash Bool := RectHash.mk (accum.hashmap.map (fun _ _ ↦ false)) accum.height accum.width
  -- if checked.geometory != grid.geometory then return (accum, dbg "!!!" 0)
  let mut to_visit := [(i, j)]
  let mut seg_h : HashSet Vec₂ := HashSet.emptyWithCapacity 100
  let mut seg_v : HashSet Vec₂ := HashSet.emptyWithCapacity 100
  while !to_visit.isEmpty do
    let p :: to_visit' := to_visit | continue
    to_visit := to_visit'
    if checked[p]? == some true then continue
    checked := checked.set p true
    if grid[p]? == some ch then
      count := count + 1
      accum := accum.set p true
      if p.fst == 0 || grid[(p.fst - 1, p.snd)]? != some ch then seg_h := seg_h.insert p
      if               grid[(p.fst + 1, p.snd)]? != some ch then seg_h := seg_h.insert (p.fst + 1, p.snd)
      if p.snd == 0 || grid[(p.fst, p.snd - 1)]? != some ch then seg_v := seg_v.insert p
      if               grid[(p.fst, p.snd + 1)]? != some ch then seg_v := seg_v.insert (p.fst, p.snd + 1)
      for dir in [Dir.N, Dir.E, Dir.S, Dir.W] do
        let q := p + dir
        if grid[q]?.isSome then to_visit := to_visit.concat q
  (accum, count * (seg_v.size + seg_h.size))

def solve (input : RectHash Char) : Nat := Id.run do
  let mut accum := RectHash.mk (input.hashmap.map (fun _ _ ↦ false)) input.height input.width
  let mut sum := 0
  for h in 0 ... input.height do
    for w in 0 ... input.width do
      let (accum', c) := evaluate_at accum input w h
      accum := accum'
      sum := sum + c
  return sum

end Part1

namespace Part2

instance : Ord (Int × Bool) where
  compare a b := match compare a.fst b.fst with
  | Ordering.eq => compare a.snd b.snd
  | cmp => cmp

def count_sides (hash : HashMap Int (Array (Int × Bool))) : Nat :=
  hash.values.iter
    |>.map (fun v' ↦ Id.run do
      let v := v'.qsortOrd
      let mut count : Nat := 1
      let mut ended := v[0]!.fst + 1
      let mut spin := v[0]!.snd
      for (st, sp) in v.iter.drop 1 do
        if ended != st || spin != sp then count := count + 1
        ended := st + 1
        spin := sp
      count)
    |>.sum

def evaluate_at (accum' : @&RectHash Bool) (grid : @&RectHash Char) (i j : Int) : RectHash Bool × Nat := Id.run do
  if accum'[(i, j)]? == some true then return (accum', 0)
  let some ch := grid[(i, j)]? | return (accum', 0)
  let mut accum := accum'
  let mut count := 0
  let mut checked : RectHash Bool := RectHash.mk (accum.hashmap.map (fun _ _ ↦ false)) accum.height accum.width
  -- if checked.geometory != grid.geometory then return (accum, dbg "!!!" 0)
  let mut to_visit := [(i, j)]
  let mut seg_h : HashMap (Vec₂ × Bool) Unit := HashMap.emptyWithCapacity 100
  let mut seg_v : HashMap (Vec₂ × Bool) Unit := HashMap.emptyWithCapacity 100
  while !to_visit.isEmpty do
    let p :: to_visit' := to_visit | continue
    to_visit := to_visit'
    if checked[p]? == some true then continue
    checked := checked.set p true
    if grid[p]? == some ch then
      count := count + 1
      accum := accum.set p true
      if p.fst == 0 || grid[(p.fst - 1, p.snd)]? != some ch then seg_h := seg_h.insert (p, false) ()
      if grid[(p.fst + 1, p.snd)]? != some ch then seg_h := seg_h.insert ((p.fst + 1, p.snd), true) ()
      if p.snd == 0 || grid[(p.fst, p.snd - 1)]? != some ch then seg_v := seg_v.insert (p, false) ()
      if grid[(p.fst, p.snd + 1)]? != some ch then seg_v := seg_v.insert ((p.fst, p.snd + 1), true) ()
      for dir in [Dir.N, Dir.E, Dir.S, Dir.W] do
        let q := p + dir
        if grid[q]?.isSome then to_visit := to_visit.concat q
  -- build longer segments
  let hss : HashMap Int (Array (Int × Bool)) := seg_h.keysIter
    |>.fold
      (fun (acc : HashMap Int (Array (Int × Bool))) ps ↦
        let (pos, spin) := ps
        acc.alter pos.fst (fun ol ↦ some <| (ol.unwrapOr #[]).push (pos.snd, spin)))
      (HashMap.emptyWithCapacity 100)
  let vss : HashMap Int (Array (Int × Bool)) := seg_v.keysIter
    |>.fold
      (fun (acc : HashMap Int (Array (Int × Bool))) ps ↦
        let (pos, spin) := ps
        acc.alter pos.snd (fun ol ↦ some <| (ol.unwrapOr #[]).push (pos.fst, spin)))
      (HashMap.emptyWithCapacity 100)
  (accum, count * (count_sides hss + count_sides vss))

def solve (input : RectHash Char) : Nat := Id.run do
  let mut accum := RectHash.mk (input.hashmap.map (fun _ _ ↦ false)) input.height input.width
  let mut sum := 0
  for h in 0 ... input.height do
    for w in 0 ... input.width do
      let (accum', c) := evaluate_at accum input h w
      accum := accum'
      sum := sum + c
  return sum

end Part2

public def solve := AocProblem.config 2024 12 parser.parse Part1.solve Part2.solve

end Y2024.Day12
