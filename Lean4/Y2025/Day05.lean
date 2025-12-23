module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2025.Day05
open Accumulation CiCL

structure Input where
  ranges : Array (Nat × Nat)
  ids : Array Nat
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.ranges}, {s.ids}"

namespace parser

open AoCParser
open Std.Internal.Parsec.String

def parse_range := do Prod.mk <$> (number <* (pchar '-')) <*> number
def parse_ids := separated number eol

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do Input.mk <$> ((separated parse_range eol) <* eol <* eol) <*> parse_ids

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.ids |>.filter (fun i ↦ input.ranges.iter.any (fun r ↦ r.fst ≤ i && i ≤ r.snd)) |>.size

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

public def solve := AocProblem.config 2025 05 parser.parse Part1.solve Part2.solve

end Y2025.Day05
