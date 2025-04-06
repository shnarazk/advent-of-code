import Std
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2024.Day01
open Accumulation

structure Input where
  line : Array (Nat × Nat)deriving BEq, Repr
instance : ToString Input where toString s := s!"{s.line.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line_parser := do
  let left ← number <* ws
  let right ← number <* eol
  return (left, right)

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← many1 line_parser
      return Input.mk v

end parser

namespace Part1

def solve (input : Input) : Nat :=
  let l : Array Nat := input.line.map (·.1) |>.heapSort (·<·)
  let r : Array Nat := input.line.map (·.2) |>.heapSort (·<·)
  l.zip r
    |>.map (fun (l, r) ↦ if l < r then r - l else l - r)
    |> sum

end Part1

namespace Part2

open Std

def solve (input : Input) : Nat :=
  let hash := input.line.map (·.2)
    |>.foldl (fun h i ↦ h.insert i (1 + h.getD i 0)) Std.HashMap.emptyWithCapacity
  input.line.map (·.1)
    |>.map (fun i ↦ i * hash.getD i 0)
    |> sum

end Part2

def solve := AocProblem.config 2024 1 parser.parse Part1.solve Part2.solve

end Y2024.Day01
