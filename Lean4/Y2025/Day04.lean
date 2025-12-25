module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

namespace Y2025.Day04

open Std Accumulation CiCL Dim2 Rect

structure Input where
  grid : Rect Bool
deriving BEq

instance : ToString Input where
  toString s := s!"{s.grid}"

def dir8 :=
  [ Dir.N.asVec₂
  , Dir.E.asVec₂
  , Dir.S.asVec₂
  , Dir.W.asVec₂
  , Dir.N + Dir.E
  , Dir.E + Dir.S
  , Dir.S + Dir.W
  , Dir.W + Dir.N ]

def depends (grid : HashSet Vec₂) (pos : Vec₂) : List Vec₂ :=
  dir8.iter.map (pos + ·) |>.filter (grid.contains ·) |>.toList

def removable (grid : HashSet Vec₂) (pos : Vec₂) : Bool :=
  (dir8.iter.filter (fun d ↦ grid.contains (pos + d))).count < 4

namespace parser

open AoCParser
open Std.Internal.Parsec.String

def parse_line := repeated ((· == '@') <$> (pchar '.' <|> pchar '@'))

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := (Input.mk ∘ Rect.of2DMatrix) <$> separated parse_line eol

end parser

namespace Part1

def solve (input : Input) : Nat := Id.run do
  let h := input.grid.enum.filter (·.snd) |>.map (·.fst) |> HashSet.ofArray
  h.iter.filter (removable h ·) |>.count

end Part1

namespace Part2

open Std

def solve (input : Input) : Nat := Id.run do
  let h := input.grid.enum.filter (fun ib ↦ ib.2) |>.map (·.fst) |> HashSet.ofArray
  let mut flow := h.iter.map (fun p ↦ (p, depends h p)) |>.toList |> HashMap.ofList
  let mut toVisit := flow.iter |>.filter (·.snd.length < 4) |>.map (·.fst) |>.toList
  let mut removed := 0
  while !toVisit.isEmpty do
    let mut nextTargets := []
    for toRemove in toVisit do
      if let some nexts := flow.get? toRemove then
        flow := flow.erase toRemove
        removed := removed + 1
        for next in nexts do
          let some depends := flow.get? next | panic! ""
          let depends' := depends.erase toRemove
          flow := flow.insert next depends'
          if depends'.length < 4 then
            nextTargets := nextTargets.insert next
    toVisit := nextTargets
  removed

end Part2

public def solve := AocProblem.config 2025 04 parser.parse Part1.solve Part2.solve

end Y2025.Day04
