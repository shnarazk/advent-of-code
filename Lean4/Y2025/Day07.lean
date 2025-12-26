module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
-- public import «AoC».Vec

namespace Y2025.Day07
open Accumulation CiCL

structure Input where
  input : Array (Array Char)
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.input}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_nmemonic := pchar '.' <|> pchar '|' <|> pchar 'S'
def parse_line := repeated parse_nmemonic
def parse_input := separated parse_line eol

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> parse_input

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

public def solve := AocProblem.config 2025 07 parser.parse Part1.solve Part2.solve

end Y2025.Day07
