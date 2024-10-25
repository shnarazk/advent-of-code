import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2023.Day16

open Accumulation CiCL TwoDimensionalVector64

structure Input where
deriving BEq, Repr

instance : ToString Input where toString _ := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := pchar '|' <|> pchar '-' <|> pchar '\\' <|> pchar '/' <|> pchar '.'

def maze_line := do
  let v ← many1 cell <* eol
  return  v -- .map (match · with | 'O' => Kind.Round | '#' => Kind.Cube | _ => Kind.Empty)

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Char)) := AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1

def solve (_ : Array (Rect Char)) : Nat := 0

end Part1

namespace Part2

def solve (_ : Array (Rect Char)) : Nat := 0

end Part2

def solve := AocProblem.config 2023 16
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day16
