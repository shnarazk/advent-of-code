module

public import Std
public import Std.Internal.Parsec
public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator

namespace Y2025.Day01

open Accumulation

structure Input where
  line : Array Int
deriving BEq, Repr
instance : ToString Input where toString s := s!"{s.line.size}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line_parser := do
  let pre ← pstring "L" <|> pstring "R"
  let num ← number_p <* eol
  return if pre == "L" then - num else num

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do Input.mk <$> many line_parser

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.line.foldl
    (fun ⟨zeros, pos⟩ step ↦
      let new := (pos + step) % 100
      ⟨zeros + if new = 0 then 1 else 0, new⟩)
    (0, 50)
  |>.fst

end Part1

namespace Part2

open Std

def solve (input : Input) : Nat :=
  input.line.foldl
    (fun ⟨zeros, pos⟩ step ↦
      let p := pos + step
      ⟨zeros + p.natAbs / 100 + if pos > 0 ∧ p ≤ 0 then 1 else 0, (p % 100 + 100) % 100⟩)
    (0, 50)
  |>.fst

end Part2

public def solve := AocProblem.config 2025 1 parser.parse Part1.solve Part2.solve

end Y2025.Day01
