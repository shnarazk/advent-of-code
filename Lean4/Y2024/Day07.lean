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
          (fun acc val ↦ [a + val, a * val].foldl (fun acc n ↦ acc.insert n) acc)
          Std.HashSet.empty
       |> (exp threshold rest ·)

def expand (threshold : Nat) (l : Array Nat) : Std.HashSet Nat :=
  exp threshold l.toList (Std.HashSet.empty.insert 0)

def solve (input : Input) : Nat :=
  dbg s!"{input.line.size}" input.line
    |>.map (fun ((val: Nat), (v: Array Nat)) ↦
      if expand val v |>.contains val then val else 0)
    |> sum

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 07 parser.parse Part1.solve Part2.solve

end Y2024.Day07
