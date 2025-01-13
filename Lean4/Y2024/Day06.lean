import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Vec

namespace Y2024.Day06

open Accumulation CiCL Dim2 Std

structure Input where
  line : Array (Array Char)
  obstruction : HashSet Idx₂
  guardPos : Idx₂
  guardDir : Dir
  size: Vec₂
deriving BEq

instance : ToString Input where toString self := s!"{self.obstruction.toList}"

namespace Input

def status (self : Input) : (Idx₂ × Dir) := (self.guardPos, self.guardDir)

def turn (self : Input) : Input := { self with guardDir := self.guardDir.turn }

def moveTo (self : Input) (pos : Idx₂) : Input := { self with guardPos := pos }

def includes (self : Input) (pos : Vec₂) : Option Idx₂ :=
  if h : (0, 0) ≤ pos ∧ pos.1 < self.size.1 ∧ pos.2 < self.size.2 then some ⟨pos, h.left⟩ else none

def nextPos (self : Input) : Option Idx₂ :=
  self.includes <| self.guardPos + self.guardDir.asVec₂

partial def loop (self : Input) (trail : HashSet (Idx₂ × Dir)) (pos : Option Idx₂) : Bool :=
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

def isLoop (self : Input) (pos : Idx₂) (pre: Idx₂ × Dir) : Bool :=
  let self' := { self with
      guardPos := pre.1,
      guardDir := pre.2,
      obstruction := (self.obstruction.insert pos) }
  self'.loop HashSet.empty pre.1

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
          (fun h (j, c) ↦ if c == '#' then h.insert (↑(i, j) : Idx₂) else h)
          h)
        (HashSet.empty : HashSet Idx₂)
      let p := v.enum.flatMap
          (fun (i, l) ↦ l.enum.flatMap (fun (j, c) ↦ if c == '^' then #[(i, j)] else #[]))
          |>.get! 0
      let size := (v.size, v[0]!.size)
      return Input.mk v h (p.1, p.2) Dir.N size

end parser

partial def traceMove (self : Input) (pre : Option (Idx₂ × Dir)) (hash : HashMap Idx₂ (Option (Idx₂ × Dir)))
    : HashMap Idx₂ (Option (Idx₂ × Dir)) :=
  let hash' := if hash.contains self.guardPos then hash else hash.insert self.guardPos pre
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

def solve (input : Input) : Nat := traceMove input none HashMap.empty |>.size

end Part1

namespace Part2

def solve (input : Input) : Nat :=
  traceMove input none HashMap.empty
    |>.filter (fun pos pre ↦ if let some p := pre then (input.isLoop pos p) else false)
    |>.size

end Part2

def solve := AocProblem.config 2024 06 parser.parse Part1.solve Part2.solve

end Y2024.Day06
