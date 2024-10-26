import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2023.Day17

open Accumulation CiCL
open TwoDimensionalVector64

structure Input where
deriving BEq, Repr

instance : ToString Input where toString _ := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line : Parser (Array Nat) := do
  let l ← many1 digit <* eol
  return l.map (fun (c : Char) ↦ (c.val - '0'.val).toNat)

def matrix := many1 line
def parse : String → Option (Rect Nat) := AoCParser.parse parse
  where
    parse := pure ∘ Rect.of2DMatrix =<< matrix
      -- let m ← matrix
      -- return Rect.of2DMatrix m

end parser

namespace Part1

def solve (_ : Rect Nat) : Nat := 0

end Part1

namespace Part2

def solve (_ : Rect Nat) : Nat := 0

end Part2

def solve := AocProblem.config 2023 17
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day17
