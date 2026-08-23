module

public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec
public import «AoC».Grid

namespace Y2024.Day10

open Std
open Accumulation
open CiCL
open Dim2
open Grid

abbrev Input := Grid Nat

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Array Nat) := many1 single_digit

def parse : String → Option (Array (Array Nat)) :=
  AoCParser.parse (separated parse_line eol)

end parser

namespace Part1

@[inline]
partial
def expand {h w : Nat} (rect : @&Grid Nat h w) (toVisit : List (Nat × Nat))
    (visited : @&Grid Bool h w := rect.map (fun _ _ _ ↦ false))
    (result : @&HashSet (Int × Int) := HashSet.emptyWithCapacity)
    : Nat :=
  match toVisit with
  | [] => result.size
  | node :: remain =>
    if rect[node]? == some 9 then expand rect remain visited (result.insert node)
      else
        let nextLevel := rect[node]! + 1
        let toVisit' := [((-1, 0) : (Int × Int)), (1, 0), (0, -1), (0, 1)]
            |>.filterMap (node +? ·)
            |>.filter (fun i ↦ i.fst < h && i.snd < w)
            |>.filter (rect[·]! == nextLevel)
            |>.filter (!visited[·]!)
        let visited' := toVisit'.foldl (fun acc p ↦ acc.set p true) visited
      expand rect (toVisit' ++ remain) visited' result

def solve (input : Array (Array Nat)) : Nat :=
  let h := input.size
  let w := input[0]!.size
  let grid : Grid Nat h w := Grid.of2DArray input
  grid.enumerate
    |>.map (fun (i, lvl) ↦ if lvl == 0 then expand grid [i] else 0)
    |>.fold (· + ·) 0

end Part1

namespace Part2

@[inline]
partial
def expand {h w : Nat} (rect : Grid Nat h w) (toVisit : List (Nat × Nat))
    (visited : @&Grid Bool h w := rect.map (fun _ _ _ ↦ false))
    (count : Nat := 0)
    : Nat :=
  match toVisit with
  | [] => count
  | node :: remain =>
    if rect[node]? == some 9 then expand rect remain visited (count + 1)
      else
        let nextLevel := rect[node]! + 1
        let toVisit' := [((-1, 0) : (Int × Int)), (1, 0), (0, -1), (0, 1)]
            |>.filterMap (node +? ·)
            |>.filter (fun i ↦ i.fst < h && i.snd < w)
            |>.filter (rect[·]! == nextLevel)
        let visited' := toVisit'.foldl (fun acc p ↦ acc.set p true) visited
      expand rect (toVisit' ++ remain) visited' count

def solve (input : Array (Array Nat)) : Nat := Id.run do
  let h := input.size
  let w := input[0]!.size
  let grid : Grid Nat h w := Grid.of2DArray input
  let mut result : Nat := 0
  for (i, lvl) in grid.enumerate do if lvl == 0 then result := result + expand grid [i]
  result

end Part2

public def solve := AocProblem.config 2024 10 parser.parse Part1.solve Part2.solve

end Y2024.Day10
