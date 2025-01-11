import «AoC».Basic
import «AoC».Parser

namespace Y2024.Day07
open Accumulation Std

abbrev Input := Array (Nat × Array Nat)

def expand (ops : Array (Nat → Nat → Nat)) (vals : HashSet Nat) (b threshold : Nat) : HashSet Nat :=
  vals.fold
    (fun acc val ↦ ops.map (· val b) |>.filter (· <= threshold) |>.foldl (·.insert ·) acc)
    HashSet.empty

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Nat × Array Nat) := do
  let head ← number <* pstring ": "
  let v ← sepBy1 number (pstring " ")
  return (head, v)

def parse : String → Option Input := AoCParser.parse (sepBy1 parse_line eol)

end parser

def exp (ops : Array (Nat → Nat → Nat)) (threshold : Nat)
    (l : List Nat)
    (subs : HashSet Nat := HashSet.empty.insert 0)
    : Nat :=
  match l with
    | [] => if subs.contains threshold then threshold else 0
    | b :: rest => expand ops subs b threshold |> (exp ops threshold rest ·)

def solve₁ (input : Input) : Nat :=
  input.map (fun (val, v) ↦ exp #[(· + ·), (· * ·)] val v.toList) |> sum

def shift (a b : Nat) (b0 : Nat := b) : Nat :=
  if b0 < 10 then a * 10 + b else shift (a * 10) b (b0 / 10)
-- #eval shift 3000000 1000000

def solve₂ (input : Input) : Nat :=
  input.map (fun (val, v) ↦ exp #[(· + ·), (· * ·), shift] val v.toList) |> sum

def solve := AocProblem.config 2024 07 parser.parse solve₁ solve₂

end Y2024.Day07
