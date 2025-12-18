module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
-- import «AoC».Rect64

namespace UInt64

/-- return the number of digits: `0.iLog10 = 1` -/
partial
def iLog10 (a : UInt64) : Int := if a < 10 then 1 else 1 + iLog10 (a / 10)

-- #eval (12809 : UInt64).iLog10

end UInt64

namespace Y2025.Day02

open Accumulation CiCL

structure Input where
  line : Array (UInt64 × UInt64)
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"


namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_range := do
  (fun (a : Nat) _ (b : Nat) ↦ (a.toUInt64, b.toUInt64)) <$> number <*> pchar '-' <*> number

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> sepBy1 parse_range (pchar ',')

end parser

namespace Part1

def calcOnRange (a b : UInt64) : Nat := (min a.iLog10  b.iLog10).toNat

def solve (input : Input) : Nat :=
  input.line.map (uncurry calcOnRange) |> sum

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

public def solve := AocProblem.config 2025 02 parser.parse Part1.solve Part2.solve

end Y2025.Day02
