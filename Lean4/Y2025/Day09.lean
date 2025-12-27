module

public import Std.Data.Iterators.Combinators.Zip
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

namespace Y2025.Day09

open Std
open Accumulation Dim2

/-- return the distance between a and b -/
def dist (a b : Int) : Nat := (if a ≤ b then b - a else a - b).toNat

/-- return one plus the distance between a and b -/
def dist₁ (a b : Int) : Nat := (1 + if a ≤ b then b - a else a - b).toNat

structure Input where
  line : Array Idx₂
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line := (fun (a b : Nat) ↦ (↑(a, b) : Idx₂)) <$> number <* pchar ',' <*> number
def parse_input := separated parse_line eol

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> parse_input

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.line.iter
    |> (fun {α : Type} (a : Iter α) ↦ (0...a.count).iter.zip a)
    |>.map (fun (i, p) ↦
      input.line.iterFromIdx (i + 1)
        |>.map (fun (q : Idx₂) ↦ (dist₁ p.val.1 q.val.1) * (dist₁ p.val.2 q.val.2))
        |>.fold (fun (a b : Nat) ↦ max a b) 0)
    |>.fold (fun (a b : Nat) ↦ max a b) 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do
  0

end Part2

public def solve := AocProblem.config 2025 09 parser.parse Part1.solve Part2.solve

end Y2025.Day09
