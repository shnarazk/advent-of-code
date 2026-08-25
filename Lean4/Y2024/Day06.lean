module

public import Itertools
public import WinnowParsers
public import «AoC».Basic
public import «AoC».Vec

namespace Y2024.Day06

open Dim2 Std

structure State where
  pos : Vec₂
  dir : Dir
deriving BEq, Hashable

instance : ToString State where toString self := s!"{self.pos}"

namespace State

@[inline]
def turn (self : State) : State := { self with dir := self.dir.turn }

@[inline]
def moveTo (self : State) (pos : Vec₂) : State := { self with pos := pos }

@[inline]
def includes (size: Vec₂) (pos : Vec₂) : Option Vec₂ :=
  if (0, 0) ≤ pos ∧ pos.1 < size.1 ∧ pos.2 < size.2 then some pos else none

/-- 移動先が領域内でなければ `none` -/
@[inline]
def nextPos (self : State) (size : Vec₂) : Option Vec₂ := includes size <| self.pos + self.dir.asVec₂

@[inline]
def nextPos! (self : State) : Vec₂ := self.pos + self.dir.asVec₂

end State

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseLine := do many1 (pchar '.' <|> pchar '#' <|> pchar '^')
-- #eval AoCParser.parse parseLine "^..#"

def parse : String → Option (State × Vec₂ × HashMap Vec₂ Unit) := AoCParser.parse parser
  where
    parser : Parser (State × Vec₂ × HashMap Vec₂ Unit) := do
      let v ← many1 (parseLine <* eol)
      let obstructions := v.iter.enumerate.fold
        (fun h (i, l) ↦ l.iter.enumerate.fold
          (fun h (j, c) ↦ if c == '#' then h.insert (↑(i, j) : Vec₂) () else h)
          h)
        (HashMap.emptyWithCapacity : HashMap Vec₂ Unit)
      let p := v.iter.enumerate
          |>.flatMap (fun (i, l) ↦ l.iter.enumerate.flatMap (fun (j, c) ↦ (if c == '^' then #[(i, j)] else #[]).iter) |>.toList.iter)
          |>.toArray
          |> (·[0]!)
      return (State.mk (p.1, p.2) Dir.N, (v.size, v[0]!.size), obstructions)

end parser

/-- 辿った場所をHashMapとして返す -/
partial
def traceMove
    (self : @& State)
    (size : Vec₂)
    (obstructions : HashMap Vec₂ Unit)
    (pre : @& Option State)
    (hash : HashMap Vec₂ State)
    : HashMap Vec₂ State :=
  let hash' := if let some p := pre
      then if !hash.contains self.pos then hash.insert self.pos p else hash
      else hash.insert self.pos self;
  match self.nextPos size with
    | none   => hash'
    | some p =>
      if obstructions.contains p
      then
        let turned := self.turn
        let pre' := some turned
        let self' := (turned.moveTo <| (turned.nextPos size).unwrapOr p)
        traceMove self' size obstructions pre' hash'
      else
        let pre' := some self
        let self' := self.moveTo p
        traceMove self' size obstructions pre' hash'

namespace Part1

def solve (data: State × Vec₂ × HashMap Vec₂ Unit) : Nat := traceMove data.1 data.2.1 data.2.2 none HashMap.emptyWithCapacity |>.size

end Part1

namespace Part2

/-- 同じ場所を辿れば`true`。`trail`に記録 -/
partial
def findLoop
    (self : @& State)
    (size : Vec₂)
    (obstructions : HashMap Vec₂ Unit)
    (new_obstruction : Vec₂)
    (trail : HashMap State Unit)
    : Bool :=
  -- nextPosに行けることは確認済み
  let self₀ := self.moveTo self.nextPos!
  if trail.contains self₀
    then true
    else
      let trail' := trail.insert self₀ ()
      if let some p := self₀.nextPos size
        then
          if obstructions.contains p || p == new_obstruction
            then
              let self₁ := self₀.turn
              if let some p' := self₁.nextPos size
                then
                  if obstructions.contains p' || p' == new_obstruction
                    then
                      let self₂ := self₁.turn
                      findLoop self₂ size obstructions new_obstruction trail'
                    else findLoop self₁ size obstructions new_obstruction trail'
                else false
            else findLoop self₀ size obstructions new_obstruction trail'
        else false

partial
def findLoopM (init : State) (size : Vec₂) (obs : HashMap Vec₂ Unit) (newOb : Vec₂) : Bool := Id.run do
  let obstructions := obs.insert newOb ()
  let mut pos := init.moveTo init.nextPos!
  let mut trail := HashMap.emptyWithCapacity
  repeat
    if trail.contains pos then return true
    trail := trail.insert pos ()
    let some p := pos.nextPos size | return false
    if obstructions.contains p then
      pos := pos.turn
      let some p' := pos.nextPos size | return false
      if obstructions.contains p' then pos := pos.turn
    pos := pos.moveTo pos.nextPos!
  return false

def isLoop (self : State) (size : Vec₂) (obs : HashMap Vec₂ Unit) (newOb : Vec₂) (pre: State) : Bool :=
  let self' := { self with pos := pre.1 - pre.2.asVec₂, dir := pre.2 }
  -- findLoopM self' size obs newOb
  findLoop self' size obs newOb HashMap.emptyWithCapacity

def solve (data : State × Vec₂ × HashMap Vec₂ Unit) : Nat :=
  traceMove data.1 data.2.1 data.2.2 none HashMap.emptyWithCapacity
    |>.filter (isLoop data.1 data.2.1 data.2.2 ·)
    |>.size

end Part2

def return0 (_: State) : Nat := 0

public def solve := AocProblem.config 2024 06 parser.parse Part1.solve Part2.solve

end Y2024.Day06
