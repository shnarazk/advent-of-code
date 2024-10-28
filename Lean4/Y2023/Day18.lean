import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
-- import «AoC».Rect64

namespace Y2023.Day18

open Accumulation CiCL

structure Input where
  dir : Char
  length : Nat
  colorCode : Nat
deriving BEq, Repr

instance : ToString Input where toString s := s!"{s.colorCode}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line := do
  let dist ← (pchar 'U' <|> pchar 'D' <|> pchar 'L' <|> pchar 'R') <* whitespaces
  let num ← number <* pstring " (#"
  let hexs ← many1 (satisfy (fun c ↦ ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')))
  let _ ← pchar ')'
  return (Input.mk
      dist
      num
      (hexs.map (fun c ↦ ("0123456789abcdef".enumerate.find? (Prod.snd · == c)) |>.mapOr (·.fst) 0)
        |>.foldl (fun (acc v : Nat) ↦ acc * 16 + v) 0))
-- #check ['o'].map (fun c ↦ "-yo".enumerate.find? (·.snd == c) |>.mapOr (·.fst) 0)

def parse : String → Option (Array Input) := AoCParser.parse parser
  where
    parser : Parser (Array Input) := sepBy1 line eol

end parser

namespace Part1

def solve (_ : Array Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Array Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 18
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day18
