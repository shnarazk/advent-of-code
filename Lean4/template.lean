module

public import Itertools
public meta import Itertools
public import WinnowParsers
public meta import WinnowParsers
public import «AoC».Basic
public meta import «AoC».Basic
public import «AoC».Combinator
-- public import «AoC».Vec

namespace Y2025.Day00

open Std

/-- The input data. -/
structure Input where
deriving BEq, Hashable, Repr

instance : ToString Input where toString _ := s!""

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := return Input.mk

#guard AoCParser.parse number "123" == some 123

end parser

namespace Part1

def solve (_ : Input) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2025 00
  ((CiCL.T dbg (fun data ↦ s!"parsed as {data}")) ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2025.Day00
