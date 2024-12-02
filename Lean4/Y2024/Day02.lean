import Std
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2024.Day02
open Accumulation

structure Input where
  line : Array (Array Nat) deriving BEq, Repr
instance : ToString Input where toString s := s!"{s.line.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line_parser := do sepBy1 number (pchar ' ')
-- #eval AoCParser.parse line_parser "3 5 8"

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← sepBy1 line_parser eol
      return Input.mk v
-- #eval parse "3 8\n1 2 3\n6 9"

end parser

def abs_diff (a b : Nat) : Nat :=
  if a < b
    then b - a
    else a - b

def between (a : Nat) (b : Nat × Nat): Bool :=
  b.1 ≤ a && a ≤ b.2

def satisfy (levels : Array Nat) : Bool :=
  (levels.windows2.all (CiCL.uncurry (· < ·))
    || levels.windows2.all (CiCL.uncurry (· > ·)))
    && levels.windows2.all (fun (a, b) ↦ between (abs_diff a b) (1, 3))

namespace Part1

def solve (input : Input) : Nat := input.line.filter satisfy |>.size

end Part1

namespace Part2

open Std

def solve (input : Input) : Nat :=
  -- input.line.filter (fun (l : Array Nat) => )
  0

end Part2

def solve := AocProblem.config 2024 2 parser.parse Part1.solve Part2.solve

end Y2024.Day02
