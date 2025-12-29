module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
-- public import «AoC».Vec

namespace Y2025.Day00

open Accumulation CiCL

structure Input where
deriving BEq, Hashable, Repr

instance : ToString Input where toString _ := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := return Input.mk

end parser

namespace Part1

def solve (_ : Input) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2025 00
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2025.Day00
