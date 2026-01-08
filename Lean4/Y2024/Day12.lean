module

public import Itertools
public import WinnowParsers
public import «AoC».Basic
public import «AoC».Vec

namespace Y2024.Day12

open Std Dim2

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

def solve (input : Input) : Nat := Id.run do
  return (dbg s!"height: {input.grid.height}" 0)

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2024 12 parser.parse Part1.solve Part2.solve

end Y2024.Day12
