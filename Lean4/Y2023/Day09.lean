import «AoC».Basic
import «AoC».Parser

namespace Y2023.Day09

open Accumulation

namespace parser

open AoCParser
open Std.Internal.Parsec.String

def parse := AoCParser.parse parser
  where
    parser := sepBy1 (sepBy1 number_signed (pchar ' ')) eol

end parser

def windows₂ (l : List α) : List (α × α) :=
  match l with
  | []          => []
  | a :: b :: c => (a, b) :: windows₂ (b :: c)
  | [_]         => []

namespace Part1

def evaluate_ (n : Nat) (a : List Int) : Int :=
  -- n is used for termination assertion
  -- or proove diff length is smaller than a's
  match n with
  | 0 => 0
  | n' + 1 =>
    let diff : List Int := windows₂ a |>.map (fun (a, b) => b - a)
    if diff.all (· == 0) then
      a.getLast!
    else
      (evaluate_ n' diff) + a.getLast!

def evaluate (a : Array Int) : Int := evaluate_ a.size a.toList

def solve (d: Array (Array Int)) : Nat := d.map evaluate |> sum

end Part1

-- #eval solve2_line ""

namespace Part2

def evaluate (n : Nat) (a : List Int) : Int :=
  -- n is used for termination assertion
  -- or proove diff length is smaller than a's
  match n with
  | 0 => 0
  | n' + 1 =>
    let diff : List Int := windows₂ a |>.map (fun (a, b) => b - a)
    if diff.all (· == 0) then a.getLast! else a[0]! - (evaluate n' diff)

def solve (d : Array (Array Int)) : Nat :=
  d.map (fun a => evaluate a.size a.toList) |> sum

end Part2

def solve := AocProblem.config 2023 9 parser.parse Part1.solve Part2.solve

end Y2023.Day09
