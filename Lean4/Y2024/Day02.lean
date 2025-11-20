module

public import Std
public import Std.Internal.Parsec
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2024.Day02
open CiCL

abbrev Input := Array (Array Nat)

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line_parser := do sepBy1 number (pchar ' ')
-- #eval AoCParser.parse line_parser "3 5 8"

def parse : String → Option Input := AoCParser.parse (sepBy1 line_parser eol)
-- #eval parse "3 8\n1 2 3\n6 9"

end parser

def abs_diff (a b : Nat) : Nat := if a < b then b - a else a - b

def between (a : Nat) (b : Nat × Nat): Bool := b.1 ≤ a && a ≤ b.2

def satisfy (levels : Array Nat) : Bool :=
  (levels.windows2.all (uncurry (· < ·)) || levels.windows2.all (uncurry (· > ·)))
    && levels.windows2.all (fun (a, b) ↦ between (abs_diff a b) (1, 3))

namespace Part1

def solve (input : Input) : Nat := input.filter satisfy |>.size

end Part1

namespace Part2

def solve (inp : Input) : Nat :=
  inp.filter (fun l ↦ satisfy l || (List.range l.size |>.map l.eraseIdx! |>.any satisfy))
    |>.size

end Part2

public def solve := AocProblem.config 2024 2 parser.parse Part1.solve Part2.solve

end Y2024.Day02
