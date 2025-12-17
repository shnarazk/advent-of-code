module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

namespace Y2024.Day06

open Accumulation CiCL Dim2 Std

structure State where
  pos : Vec₂
  dir : Dir
deriving BEq, Hashable

instance : ToString State where toString self := s!"{self.pos}"

namespace State

def turn (self : State) : State := { self with dir := self.dir.turn }

def moveTo (self : State) (pos : Vec₂) : State := { self with pos := pos }

def includes (size: Vec₂) (pos : Vec₂) : Option Vec₂ :=
  if (0, 0) ≤ pos ∧ pos.1 < size.1 ∧ pos.2 < size.2 then some pos else none

/-- 移動先が領域内でなければ `none` -/
def nextPos (self : State) (size : Vec₂) : Option Vec₂ := includes size <| self.pos + self.dir.asVec₂

def nextPos! (self : State) (size : Vec₂) : Vec₂ := self.pos + self.dir.asVec₂

end State

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseLine := do many1 (pchar '.' <|> pchar '#' <|> pchar '^')
-- #eval AoCParser.parse parseLine "^..#"

def parse : String → Option (State × Vec₂ × HashSet Vec₂) := AoCParser.parse parser
  where
    parser : Parser (State × Vec₂ × HashSet Vec₂) := do
      let v ← many1 (parseLine <* eol)
      let obstructions := v.enum.foldl
        (fun h (i, l) ↦ l.enum.foldl
          (fun h (j, c) ↦ if c == '#' then h.insert (↑(i, j) : Vec₂) else h)
          h)
        (HashSet.emptyWithCapacity : HashSet Vec₂)
      let p := v.enumerate.flatMap
          (fun (i, l) ↦ l.enum.flatMap (fun (j, c) ↦ if c == '^' then #[(i, j)] else #[]))
          |> (·[0]!)
      return (State.mk (p.1, p.2) Dir.N, (v.size, v[0]!.size), obstructions)

end parser

/-- 辿った場所をHashMapとして返す -/
partial
def traceMove
    (self : State)
    (size : Vec₂)
    (obstructions : HashSet Vec₂)
    (pre : Option State)
    (hash : HashMap Vec₂ State)
    : HashMap Vec₂ State :=
  let hash' := if let some p := pre
      then if !hash.contains self.pos then hash.insert self.pos p else hash
      else hash.insert self.pos self
  match self.nextPos size with
    | none   => hash'
    | some p =>
      if obstructions.contains p
      then
        let self' := self.turn
        traceMove (self'.moveTo <| (self'.nextPos size).unwrapOr p) size obstructions (some self') hash'
      else
        traceMove (self.moveTo p) size obstructions (some self) hash'

namespace Part1

def solve (data: State × Vec₂ × HashSet Vec₂) : Nat := traceMove data.1 data.2.1 data.2.2 none HashMap.emptyWithCapacity |>.size

end Part1

namespace Part2

/-- 同じ場所を辿れば`true`。`trail`に記録 -/
partial
def loop
    (self : State)
    (size : Vec₂)
    (obstructions : HashSet Vec₂)
    (new_obstruction : Vec₂)
    (trail : HashSet State)
    : Bool :=
  -- nextPosに行けることは確認済み
  let p := self.nextPos! size
  let self₀ := self.moveTo p
  if trail.contains self₀
    then true
    else
      let trail' := trail.insert self₀
      if let some p' := self₀.nextPos size
        then
          if obstructions.contains p' || p' == new_obstruction
            then
              let self₁ := self₀.turn
              if let some p'' := self₁.nextPos size
                then
                  if obstructions.contains p'' || p'' == new_obstruction
                    then
                      let self₂ := self₁.turn
                      loop self₂ size obstructions new_obstruction trail'
                    else loop self₁ size obstructions new_obstruction trail'
                else false
            else loop self₀ size obstructions new_obstruction trail'
        else false

def isLoop
    (self : State)
    (size : Vec₂)
    (obstructions : HashSet Vec₂)
    (new_obstruction : Vec₂)
    (pre: State)
    : Bool :=
  let self' := { self with pos := pre.1 - pre.2.asVec₂, dir := pre.2 }
  loop self' size obstructions new_obstruction HashSet.emptyWithCapacity

def solve (data : State × Vec₂ × HashSet Vec₂) : Nat :=
  traceMove data.1 data.2.1 data.2.2 none HashMap.emptyWithCapacity |>.filter (isLoop data.1 data.2.1 data.2.2 ·) |>.size

end Part2

def return0 (_: State) : Nat := 0

public def solve := AocProblem.config 2024 06 parser.parse Part1.solve Part2.solve

end Y2024.Day06
