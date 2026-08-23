module

public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec

namespace Y2024.Day10
open Accumulation CiCL Dim2 Std

abbrev Input := Rect Nat

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Array Nat) := many1 single_digit

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Rect.of2DMatrix <$> separated parse_line eol

end parser

namespace Part1

partial
def expand (rect : Rect Nat) (toVisit : List Idx₂)
    (visited : Rect Bool := rect.map (K false))
    (result : HashSet Vec₂ := HashSet.emptyWithCapacity)
    : Nat :=
  match toVisit with
  | [] => result.size
  | node :: remain =>
    if rect[node]? == some 9 then expand rect remain visited (result.insert node)
      else
        let nextLevel := rect[node]! + 1
        let toVisit' := [((-1, 0) : Vec₂), (1, 0), (0, -1), (0, 1)]
            |>.filterMap (fun offset ↦ (↑ (node + offset) : Option Idx₂))
            |>.filter rect.validIndex?
            |>.filter (rect[·]? == some nextLevel)
            |>.filter (!visited[·]!)
        let visited' := toVisit'.foldl (fun acc p ↦ acc.set p true) visited
      expand rect (toVisit' ++ remain) visited' result

def solve (input : Input) : Nat :=
  input.enum |>.map (fun (p, lvl) ↦ if lvl == 0 then expand input [p] else 0) |> sum

end Part1

namespace Part2

partial
def expand (rect : Rect Nat) (toVisit : List Idx₂)
    (visited : Rect Bool := rect.map (K false))
    (count : Nat := 0)
    : Nat :=
  match toVisit with
  | [] => count
  | node :: remain =>
    if rect[node]? == some 9 then expand rect remain visited (count + 1)
      else
        let nextLevel := rect[node]! + 1
        let toVisit' := [((-1, 0) : Vec₂), (1, 0), (0, -1), (0, 1)]
            |>.filterMap (fun offset ↦ (↑ (node + offset) : Option Idx₂))
            |>.filter rect.validIndex?
            |>.filter (rect[·]? == some nextLevel)
        let visited' := toVisit'.foldl (fun acc p ↦ acc.set p true) visited
      expand rect (toVisit' ++ remain) visited' count

def solve (input : Input) : Nat :=
  input.enum |>.map (fun (p, lvl) ↦ if lvl == 0 then expand input [p] else 0) |> sum

end Part2

public def solve := AocProblem.config 2024 10 parser.parse Part1.solve Part2.solve

end Y2024.Day10
