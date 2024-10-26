import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

open Accumulation CiCL TwoDimensionalVector64

def Bool.map {α : Type} (self : Bool) (f : Unit → α) : Option α :=
  match self with
  | true  => some (f ())
  | false => none
-- #eval true.map (K 3)

namespace Y2023.Day16

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
  toString (r : Rect Kind) : String :=
    r.to2Dmatrix.map (fun l ↦ l.map toString |> String.join)
      |>.map (· ++ "\n")
      |>String.join

inductive Dir where
| N | E | S | W
deriving BEq, Repr

def propagate (r : Rect Kind) (pos : Dim2) (dir : Dir) : Option (Dim2 × Dir) :=
  let k := r.get pos.fst pos.snd Kind.E
  let w := r.width
  let h := r.height
  match dir, k with
    | Dir.N, Kind.V => some (pos, dir)
    | Dir.N, Kind.H => some (pos, dir)
    | Dir.N, Kind.S => some (pos, dir)
    | Dir.N, Kind.B => some (pos, dir)
    | Dir.N, Kind.E => (0 < pos.fst : Bool).map (K ((pos.fst - 1, pos.snd), dir))

    | Dir.E, Kind.V => some (pos, dir)
    | Dir.E, Kind.H => some (pos, dir)
    | Dir.E, Kind.S => some (pos, dir)
    | Dir.E, Kind.B => some (pos, dir)
    | Dir.E, Kind.E => (pos.snd < w : Bool).map (K ((pos.fst, pos.snd + 1), dir))

    | Dir.S, Kind.V => some (pos, dir)
    | Dir.S, Kind.H => some (pos, dir)
    | Dir.S, Kind.S => some (pos, dir)
    | Dir.S, Kind.B => some (pos, dir)
    | Dir.S, Kind.E => (pos.fst < h : Bool).map (K ((pos.fst + 1, pos.snd), dir))

    | Dir.W, Kind.V => some (pos, dir)
    | Dir.W, Kind.H => some (pos, dir)
    | Dir.W, Kind.S => some (pos, dir)
    | Dir.W, Kind.B => some (pos, dir)
    | Dir.W, Kind.E => (0 < pos.snd : Bool).map (K ((pos.fst, pos.snd - 1), dir))

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
