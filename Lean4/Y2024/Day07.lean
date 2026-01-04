module

public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator

namespace Y2024.Day07
open Accumulation Std

abbrev Input := Array (Nat × Array Nat)

def expand (ops : Array (Nat → Nat → Nat)) (vals : HashSet Nat) (b threshold : Nat) : HashSet Nat :=
  vals.fold
    (fun acc val ↦ ops.map (· val b) |>.filter (· <= threshold) |>.foldl (·.insert ·) acc)
    HashSet.emptyWithCapacity

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Nat × Array Nat) := do
  Prod.mk <$> (number <* pstring ": ") <*> (separated number (pstring " "))

def parse : String → Option Input := AoCParser.parse (separated parse_line eol)

end parser

def exp
    (ops : Array (Nat → Nat → Nat))
    (threshold : Nat)
    (l : List Nat)
    (subs : HashSet Nat := HashSet.emptyWithCapacity.insert 0)
    : Nat :=
  match l with
    | [] => if subs.contains threshold then threshold else 0
    | b :: rest => expand ops subs b threshold |> (exp ops threshold rest ·)

def solve₁ (input : Input) : Nat :=
  input.map (fun (val, v) ↦ exp #[(· + ·), (· * ·)] val v.toList) |> sum

def shift (a b : Nat) (b0 : Nat := b) : Nat :=
  if b0 < 10 then a * 10 + b else shift (a * 10) b (b0 / 10)

#guard shift 3000000 1000000 == 30000001000000

namespace Part2

open Batteries CiCL

def search (goal : Nat) (numbers : Array Nat) : Nat := Id.run do
  let end_index := numbers.size
  let mut to_visit : BinaryHeap (Nat × Nat) _ := BinaryHeap.empty (fun (a b : Nat × Nat) ↦ a.1 < b.1)
  to_visit := to_visit.insert (numbers[0]!, 1)
  repeat
    let some state := to_visit.max | break
    to_visit := to_visit.popMax
    if state.2 == end_index
    then
      if state.1 == goal then return goal
    else
      let operand := numbers[state.2]!
      for next in [state.1 + operand, state.1 * operand, shift state.1 operand] do
        if next ≤ goal then to_visit := to_visit.insert (next, state.2 + 1)
  return 0

def solve (input : Input) : Nat := input.map (uncurry search) |> sum

end Part2

public def solve := AocProblem.config 2024 07 parser.parse solve₁ Part2.solve

end Y2024.Day07
