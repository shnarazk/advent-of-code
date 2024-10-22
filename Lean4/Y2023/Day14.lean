import Std
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect
open Std Accumulation CiCL BQN
open TwoDimensionalVector

inductive Kind where
  | Round : Kind
  | Cube  : Kind
  | Empty : Kind
deriving BEq, Repr, Hashable

instance : Inhabited Kind where default := .Empty

instance : ToString Kind where
  toString : Kind → String
  | Kind.Round => "O"
  | Kind.Cube  => "#"
  | Kind.Empty => "."

inductive Dir where
  | N : Dir
  | E : Dir
  | S : Dir
  | W : Dir
deriving BEq, Repr

def Dir.rotate (self : Dir) : Dir :=
  match self with
  | .N => .E
  | .E => .S
  | .S => .W
  | .W => .N

def Dir.to_dim2 (self : Dir) : Dim2 :=
  match self with
  | .N => Dim2.mk 0 1
  | .E => Dim2.mk 1 0
  | .S => Dim2.mk 0 (-1)
  | .W => Dim2.mk (-1) 0

#eval Dir.N.rotate.rotate.rotate.rotate

namespace TwoDimensionalVector.Rect

def pullUp (self : Rect Kind) (dir : Dir) : Rect Kind :=
  match dir with
  | .N =>
    (List.range self.shape.x.toNat).foldl
      (fun (m, filled) y ↦
        (List.range self.shape.y.toNat).foldl
          (fun (m, filled) x ↦
            match self.get (Dim2.mk y x) Kind.Empty with
            | Kind.Round => (m.swap (Dim2.mk filled x) (Dim2.mk y x), filled + 1)
            | Kind.Cube  => (m, y)
            | Kind.Empty => (m, filled))
          (m, filled)
        )
      (self, 0)
    |>.fst
  | _ => self

end TwoDimensionalVector.Rect

namespace Y2023.Day14
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
