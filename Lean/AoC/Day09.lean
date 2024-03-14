import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day09
open Std Accumulation

namespace parser
open Lean.Parsec AoCParser

def parser := sepBy1 (sepBy1 number_signed (pchar ' ')) eol

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
    if diff.all (· == 0)
    then a.getLast!
    else (evaluate_ n' diff) + a.getLast!

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

end Day09

def day09 (ext : Option String) : IO Answers := do
  if let some d := AoCParser.parse Day09.parser.parser (← dataOf 2023 9 ext)
  then return (s!"{Day09.Part1.solve d}", s!"{Day09.Part2.solve d}")
  else return ("parse error", "")
