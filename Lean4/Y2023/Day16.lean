import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2023.Day16

open Accumulation CiCL TwoDimensionalVector64

inductive Kind where
| V | H | S | B | E
deriving BEq, Repr

instance : ToString Kind where
  toString : Kind → String
    | .V => "|"
    | .H => "-"
    | .S => "/"
    | .B => "\\"
    | .E => "."

instance : ToString (Rect Kind) where
  toString (r :Rect Kind) : String :=
    r.to2Dmatrix.map (fun l ↦ l.map toString |> String.join)
      |>.map (· ++ "\n")
      |>String.join

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := do
  let c ← pchar '|' <|> pchar '-' <|> pchar '\\' <|> pchar '/' <|> pchar '.'
  return match c with
    | '|' => Kind.V
    | '-' => Kind.H
    | '/' => Kind.S
    | '\\' => Kind.B
    | _   => Kind.E

def maze_line := many1 cell <* eol

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Kind)) := AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1

def solve (_ : Array (Rect Kind)) : Nat := 0

end Part1

namespace Part2

def solve (_ : Array (Rect Kind)) : Nat := 0

end Part2

def solve := AocProblem.config 2023 16
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day16
