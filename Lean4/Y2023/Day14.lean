import Std
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect

namespace Y2023.Day14

open Std Accumulation CiCL BQN
open TwoDimensionalVector

inductive Kind where
  | Round : Kind
  | Cube  : Kind
  | Empty : Kind 
deriving BEq, Repr

instance : ToString Kind where
  toString : Kind → String
  | Kind.Round => "O"
  | Kind.Cube  => "#"
  | Kind.Empty => "."

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := pchar 'O' <|> pchar '#' <|> pchar '.'

def maze_line := do
  let v ← many1 cell <* eol
  return (dbg "line" v).map (match · with | 'O' => Kind.Round | '#' => Kind.Cube | _ => Kind.Empty)

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Kind)) := AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 14
  ((dbg "parsed") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day14
