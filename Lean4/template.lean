import Std
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y20XX.DayXX

open Std Accumulation CiCL

structure Input where
deriving BEq, Repr

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

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 11
  ((train toString dbgTrace K) ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y20XX.DayXX
