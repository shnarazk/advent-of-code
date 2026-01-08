module

public import Itertools
public import WinnowParsers
public import «AoC».Basic

namespace Y2024.Day11

open Std

structure Input where
  line: Array Nat
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> separated number (pchar ' ')

end parser

namespace Part1

def solve (input : Input) : Nat := input.line.iter.map (fun _ ↦ 1) |>.sum

end Part1

namespace Part2

def solve (input : Input) : Nat := input.line.iter.map (fun _ ↦ 1) |>.sum

end Part2

public def solve := AocProblem.config 2024 11 parser.parse Part1.solve Part2.solve

end Y2024.Day11
