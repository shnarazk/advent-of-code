module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

namespace Y2024.Day06

open Accumulation CiCL Dim2 Std

structure Input where
  guardPos : Idx₂
  guardDir : Dir
  size: Vec₂
deriving BEq

instance : ToString Input where toString self := s!"{self.guardPos}"

namespace Input

def status (self : Input) : Idx₂ × Dir := (self.guardPos, self.guardDir)

def turn (self : Input) : Input := { self with guardDir := self.guardDir.turn }

def moveTo (self : Input) (pos : Idx₂) : Input := { self with guardPos := pos }

def includes (self : Input) (pos : Vec₂) : Option Idx₂ :=
  if h : (0, 0) ≤ pos ∧ pos.1 < self.size.1 ∧ pos.2 < self.size.2 then some ⟨pos, h.left⟩ else none

/-- 移動先が領域内でなければ `none` -/
def nextPos (self : Input) : Option Idx₂ := self.includes <| self.guardPos + self.guardDir.asVec₂

end Input

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseLine := do many1 (pchar '.' <|> pchar '#' <|> pchar '^')
-- #eval AoCParser.parse parseLine "^..#"

def parse : String → Option (Input × HashSet Idx₂) := AoCParser.parse parser
  where
    parser : Parser (Input × HashSet Idx₂) := do
      let v ← many1 (parseLine <* eol)
      let obstructions := v.enum.foldl
        (fun h (i, l) ↦ l.enum.foldl
          (fun h (j, c) ↦ if c == '#' then h.insert (↑(i, j) : Idx₂) else h)
          h)
        (HashSet.emptyWithCapacity : HashSet Idx₂)
      let p := v.enumerate.flatMap
          (fun (i, l) ↦ l.enum.flatMap (fun (j, c) ↦ if c == '^' then #[(i, j)] else #[]))
          |> (·[0]!)
      let size := (v.size, v[0]!.size)
      return (Input.mk (p.1, p.2) Dir.N size, obstructions)

end parser

/-- 辿った場所をHashMapとして返す -/
partial
def traceMove (self : Input) (obstructions : HashSet Idx₂) (pre : Option (Idx₂ × Dir)) (hash : HashMap Idx₂ (Idx₂ × Dir))
    : HashMap Idx₂ (Idx₂ × Dir) :=
  let hash' := if let some p := pre
      then if !hash.contains self.guardPos then hash.insert self.guardPos p else hash
      else hash.insert self.guardPos (self.guardPos, self.guardDir)
  match self.nextPos with
    | none   => hash'
    | some p =>
      if obstructions.contains p
      then
        let self' := self.turn
        traceMove (self'.moveTo <| self'.nextPos.unwrapOr p) obstructions (some self'.status) hash'
      else
        traceMove (self.moveTo p) obstructions (some self.status) hash'

namespace Part1

def solve (data: Input × HashSet Idx₂) : Nat := traceMove data.1 data.2 none HashMap.emptyWithCapacity |>.size

end Part1

namespace Part2

structure Guard where
  guardPos : Idx₂
  guardDir : Dir
  size: Vec₂
deriving BEq

/-- 同じ場所を辿れば`true`。`trail`に記録 -/
partial
def loop (self : Input) (obstructions : HashSet Idx₂) (new_obstruction : Idx₂) (trail : HashSet (Idx₂ × Dir)) (nextPos : Option Idx₂) : Bool :=
  match nextPos with
    | none   => false
    | some p =>
      let self₀ := self.moveTo p
      if trail.contains self₀.status -- && !self₀.obstruction.contains p
        then true
        else
          let trail' := trail.insert self₀.status
          if let q@(some p') := self₀.nextPos
            then
              if obstructions.contains p' || p' == new_obstruction
                then
                  let self₁ := self₀.turn
                  if let q'@(some p'') := self₁.nextPos
                    then
                      if obstructions.contains p'' || p'' == new_obstruction
                        then
                          let self₂ := self₁.turn
                          loop self₂ obstructions new_obstruction trail' self₂.nextPos
                        else loop self₁ obstructions new_obstruction  trail' q'
                    else false
                else loop self₀ obstructions new_obstruction trail' q
            else false

def isLoop (self : Input) (obstructions : HashSet Idx₂) (new_obstruction : Idx₂) (pre: Idx₂ × Dir) : Bool :=
  let self' := { self with guardPos := pre.1, guardDir := pre.2 }
  loop self' obstructions new_obstruction HashSet.emptyWithCapacity pre.1

def solve (data : Input × HashSet Idx₂) : Nat :=
  traceMove data.1 data.2 none HashMap.emptyWithCapacity |>.filter (isLoop data.1 data.2 ·) |>.size

end Part2

def return0 (_: Input) : Nat := 0

public def solve := AocProblem.config 2024 06 parser.parse Part1.solve Part2.solve

end Y2024.Day06
