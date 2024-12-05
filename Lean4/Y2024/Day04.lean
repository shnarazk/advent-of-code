import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2024.Day04

open Accumulation CiCL
abbrev HashMap := Std.HashMap

structure Input where
  line: Array String
deriving BEq, Repr

instance : ToString Input where toString _ := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser String := alphabets
-- #eval AoCParser.parse alphabets "eocb\n"

def parse_lines := sepBy1 parse_line eol
-- #eval AoCParser.parse parse_lines "eocb\nABC\n"

def parse : String → Option Input := AoCParser.parse parser
  where parser := do
    let v ← parse_lines
    return Input.mk v
-- #eval parse "ABC\nXYZ"

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 04
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day04
