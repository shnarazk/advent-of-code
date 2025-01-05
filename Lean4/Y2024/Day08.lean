import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2024.Day08

open Std Accumulation CiCL TwoDimensionalVector64

structure Input where
  anntena : List ((Nat × Nat) × Char)
deriving BEq, Hashable, Repr
-- #check ((4, 8) : Dim2)

instance : ToString Input where toString s := s!"{s.anntena}"

namespace parser

open Std
open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseSymbol := do asciiLetter <|> digit <|> pchar '.'

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← sepBy1 (many1 parseSymbol) eol
      let a := v.enum.toList.map
        (fun (i, row) ↦ row.enum.toList.map (fun (j, c) ↦ ((i, j), c)))
        |>.flatten
        |>.filter (fun (_, c) ↦ c ≠ '.')
      return Input.mk a

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.anntena
    |>.foldl
        (fun (h : HashSet Dim2) _anntena ↦ h)
        HashSet.empty
    |>.size

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 08
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day08
