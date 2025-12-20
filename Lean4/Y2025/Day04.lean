module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

namespace Y2025.Day04
open Std Accumulation CiCL Dim2 Rect

structure Input where
  grid: Rect Bool
deriving BEq

instance : ToString Input where toString s := s!"{s.grid}"

def removable (grid : HashSet Vec₂) (pos : Vec₂) : Bool :=
  ([
    Dir.N.asVec₂,
    Dir.E.asVec₂,
    Dir.S.asVec₂,
    Dir.W.asVec₂,
    Dir.N.asVec₂+ Dir.E.asVec₂,
    Dir.E.asVec₂+ Dir.S.asVec₂,
    Dir.S.asVec₂+ Dir.W.asVec₂,
    Dir.W.asVec₂+ Dir.N.asVec₂,
  ].iter.filter (fun d ↦ grid.contains (pos + d))).count < 4


namespace parser

open AoCParser
open Std.Internal.Parsec.String

def parse_line := repeated ((· == '@') <$> (pchar '.' <|> pchar '@'))

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := builder <$> separated parse_line eol
    builder := fun v ↦ Input.mk (Rect.of2DMatrix v)

end parser

namespace Part1

def solve (input : Input) : Nat := Id.run do
  let l := input.grid.enum.filter (fun ib ↦ ib.2) |>.map (·.fst)
  let h := HashSet.ofArray l
  h.iter.filter (removable h ·) |>.count

end Part1

namespace Part2

open Std

def solve (input : Input) : Nat := Id.run do
  let l := input.grid.enum.filter (fun ib ↦ ib.2) |>.map (·.fst)
  let h := HashSet.ofArray l
  h.size

end Part2

public def solve := AocProblem.config 2025 04 parser.parse Part1.solve Part2.solve

end Y2025.Day04
