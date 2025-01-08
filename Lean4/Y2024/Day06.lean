import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

abbrev Vec2 := Int × Int

instance : HAdd Vec2 Vec2 Vec2 where
  hAdd a b := (a.1 + b.1, a.2 + b.2)

namespace Y2024.Day06

open Accumulation CiCL

inductive Dir
  | N
  | E
  | S
  | W
deriving BEq, Hashable, Repr

namespace Dir
def turn : Dir → Dir
  | Dir.N => Dir.E
  | Dir.E => Dir.S
  | Dir.S => Dir.W
  | Dir.W => Dir.N
-- #eval Dir.E.turn

def asVec2 : Dir → Vec2
  | Dir.N => (-1,  0)
  | Dir.E => ( 0,  1)
  | Dir.S => ( 1,  0)
  | Dir.W => ( 0, -1)
-- #eval (8, 5) + Dir.N.asVec2

instance : ToString Dir where
  toString
    | Dir.N => "N"
    | Dir.E => "E"
    | Dir.S => "S"
    | Dir.W => "W"

end Dir

structure Input where
  line : Array (Array Char)
  obstruction : Std.HashSet Vec2
  guardPos : Vec2
  guardDir : Dir
  size: Vec2
deriving BEq, Repr

instance : ToString Input where toString self := s!"{self.obstruction.toList}"

namespace Input

def status (self : Input) : (Vec2 × Dir) := (self.guardPos, self.guardDir)

def turn (self : Input) : Input := { self with guardDir := self.guardDir.turn }

def moveTo (self : Input) (pos : Vec2) : Input := { self with guardPos := pos }

def includes (self : Input) (pos : Vec2) : Option Vec2 :=
  if 0 ≤ pos.1 && pos.1 < self.size.1 && 0 ≤ pos.2 && pos.2 < self.size.2
    then some pos
    else none

def nextPos (self : Input) : Option Vec2 :=
  self.includes <| self.guardPos + self.guardDir.asVec2

partial def loop (self : Input) (trail : Std.HashSet (Vec2 × Dir)) (pos : Option Vec2) : Bool :=
  match pos with
    | none   => false
    | some p =>
      let self₀ := self.moveTo p
      if trail.contains self₀.status -- && !self₀.obstruction.contains p
        then true
        else
          let trail' := trail.insert self₀.status
          if let some p' := self₀.nextPos
            then
              if self₀.obstruction.contains p'
                then
                  let self₁ := self₀.turn
                  if let some p'' := self₁.nextPos
                    then
                        if self₁.obstruction.contains p''
                            then
                              let self₂ := self₁.turn
                              self₂.loop trail' self₂.nextPos
                            else self₁.loop trail' self₁.nextPos
                    else false
                else self₀.loop trail' self₀.nextPos
            else false

def isLoop (self : Input) (pos : Vec2) (pre: Vec2 × Dir) : Bool :=
  let self' := { self with
      guardPos := pre.1,
      guardDir := pre.2,
      obstruction := (self.obstruction.insert pos) }
  self'.loop Std.HashSet.empty pre.1

end Input

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseLine := do
  many1 (pchar '.' <|> pchar '#' <|> pchar '^')
-- #eval AoCParser.parse parseLine "^..#"

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← many1 (parseLine <* eol)
      let h := v.enum.foldl
        (fun h (i, l) ↦ l.enum.foldl
          (fun h (j, c) ↦ if c == '#' then h.insert ((i : Int), (j : Int)) else h)
          h)
        Std.HashSet.empty
      let p := v.enum.flatMap
          (fun (i, l) ↦ l.enum.flatMap (fun (j, c) ↦ if c == '^' then #[(i, j)] else #[]))
          |>.get! 0
      let size := ((v.size : Int), (v[0]!.size : Int))
      return Input.mk v h ((p.1 : Int), (p.2 : Int)) Dir.N size

end parser

partial def traceMove
    (self : Input)
    (pre : Option (Vec2 × Dir))
    (hash : Std.HashMap Vec2 (Option (Vec2 × Dir)))
    : Std.HashMap Vec2 (Option (Vec2 × Dir)) :=
  let hash' := if hash.contains self.guardPos
      then hash
      else hash.insert self.guardPos pre
  match self.nextPos with
    | none   => hash'
    | some p =>
      if self.obstruction.contains p
      then
        let self' := self.turn
        traceMove (self'.moveTo <| self'.nextPos.unwrapOr p) (some self'.status) hash'
      else
        traceMove (self.moveTo p) (some self.status) hash'

namespace Part1

def solve (input : Input) : Nat :=
  traceMove input none Std.HashMap.empty
    |>.size

end Part1

namespace Part2

def solve (input : Input) : Nat :=
  traceMove input none Std.HashMap.empty
    |>.filter (fun pos pre ↦ if let some p := pre then (input.isLoop pos p) else false)
    |>.size

end Part2

def solve := AocProblem.config 2024 06 parser.parse Part1.solve Part2.solve

end Y2024.Day06
