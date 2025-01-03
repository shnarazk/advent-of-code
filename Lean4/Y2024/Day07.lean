import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
-- import «AoC».Rect64

namespace Y2024.Day07

open Accumulation CiCL

structure Input where
  line : Array (Nat × Array Nat)
deriving BEq,Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Nat × Array Nat) := do
  let head ← number <* pstring ": "
  let v ← sepBy1 number (pstring " ")
  return (head, v)

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> (sepBy1 parse_line eol)

end parser

namespace Part1

def exp (threshold : Nat) (l : List Nat) (subs : Std.HashSet Nat) : Std.HashSet Nat :=
  match l with
    | [] => subs
    | a :: rest =>
      subs.fold
            (fun acc val ↦ [val + a, val * a]
              |>.filter (· <= threshold)
              |>.foldl (fun acc n ↦ acc.insert n) acc)
            Std.HashSet.empty
        |> (exp threshold rest ·)

def expand (threshold : Nat) (l : Array Nat) : Std.HashSet Nat :=
  exp threshold l.toList (Std.HashSet.empty.insert 0)

def solve (input : Input) : Nat :=
  input.line
    |>.map (fun ((val: Nat), (v: Array Nat)) ↦
      if expand val v |>.contains val then val else 0)
    |> sum

end Part1

namespace Part2

def shift₀ (a b b0 : Nat) : Nat :=
  if b0 < 10 then a * 10 + b else shift₀  (a * 10) b (b0 / 10)
def shift (a b : Nat) : Nat := shift₀ a b b
-- #eval shift 3000000 1000000

def exp (threshold : Nat) (l : List Nat) (subs : Std.HashSet Nat) : Std.HashSet Nat :=
  match l with
    | [] => subs
    | a :: rest =>
      subs.fold
            (fun acc val ↦ [val + a, val * a, shift val a]
              |>.filter (· <= threshold)
              |>.foldl (fun acc n ↦ acc.insert n) acc)
            Std.HashSet.empty
        |> (exp threshold rest ·)

def expand (threshold : Nat) (l : Array Nat) : Std.HashSet Nat :=
  exp threshold l.toList (Std.HashSet.empty.insert 0)

def solve (input : Input) : Nat :=
  input.line
    |>.map (fun ((val: Nat), (v: Array Nat)) ↦
      if expand val v |>.contains val then val else 0)
    |> sum

end Part2

def solve := AocProblem.config 2024 07 parser.parse Part1.solve Part2.solve

end Y2024.Day07
