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

-- notation:50 lhs " _ " rhs => Dim2.mk lhs rhs
-- #eval 30 _ 40

def pullUp (self : Rect Kind) (dir : Dir) : Rect Kind :=
  match dir with
  | .N =>
    (List.range self.shape.x.toNat).foldl
      (fun m x ↦
        (List.range self.shape.y.toNat).foldl
          (fun (m, empty) y ↦
            match m.get (Dim2.mk y x) Kind.Empty with
            | Kind.Round => (m.swap (Dim2.mk empty x) (Dim2.mk y x), empty + 1)
            | Kind.Cube  => (m, y + 1)
            | Kind.Empty => (m, empty))
          (m, 0)
        |>.fst)
      self
  | _ => dbg "?" self

def evaluate (self : Rect Kind) : Nat :=
  let height : Nat := self.shape.y.toNat
  (List.range self.shape.y.toNat).foldl
    (fun c y ↦
      (List.range self.shape.x.toNat).foldl
        (fun c x ↦
          match self.get (Dim2.mk (Int.ofNat y) (Int.ofNat x)) Kind.Empty with
          | Kind.Round => c + height - y
          | Kind.Cube  => c
          | Kind.Empty => c)
        c)
    (0 : Nat)

end TwoDimensionalVector.Rect

namespace Y2023.Day14
namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := pchar 'O' <|> pchar '#' <|> pchar '.'

def maze_line := do
  let v ← many1 cell <* eol
  return  v.map (match · with | 'O' => Kind.Round | '#' => Kind.Cube | _ => Kind.Empty)

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Kind)) := AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1
open TwoDimensionalVector.Rect

def solve (as: Array (Rect Kind)) : Nat := as.map (·.pullUp Dir.N |>.evaluate) |>sum

end Part1

namespace Part2
open TwoDimensionalVector.Rect

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 14 parser.parse Part1.solve Part2.solve

end Y2023.Day14
