import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2024.Day04

open Accumulation CiCL
abbrev HashMap := Std.HashMap

structure Input where
  plane : HashMap (Nat × Nat) Char
deriving Repr

instance : ToString Input where toString self := s!"{self.plane.toList}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Array Char) := do
  let as ← alphabets
  return as.toList.toArray
-- #eval AoCParser.parse parse_line "eocb\n"

def parse_lines := sepBy1 parse_line eol
-- #eval AoCParser.parse parse_lines "eocb\nABC\n"

def parse : String → Option Input := AoCParser.parse parser
  where parser := do
    let v ← parse_lines
    let h := v.toList.enum.map (fun (i, l) ↦ l.toList.enum.map (fun (x : Nat × Char) ↦ ((i, x.1), x.2)))
      |>.flatten
    return Input.mk (h.foldl (fun h (p, v) ↦ h.insert p v) Std.HashMap.empty)
-- #eval parse "ABC\nXYZ"

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.plane.toList.filter
      (fun (_p, _c) ↦ true)
    |>.length

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 04
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day04
