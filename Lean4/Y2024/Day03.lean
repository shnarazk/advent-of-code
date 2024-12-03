import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
-- import «AoC».Rect64

namespace Y2024.Day03

open Accumulation CiCL

inductive Inst
  | Do
  | Dont
  | Mul (vals : Nat × Nat)
deriving BEq, Repr

structure Input where
  seq : Array Inst
deriving BEq, Repr

instance : ToString Input where toString s := s!"{s.seq.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := return Input.mk #[]

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 03
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day03
