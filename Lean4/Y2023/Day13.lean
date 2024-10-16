import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».BoundedPlane

namespace Y2023.Day13

open Std Accumulation CoP CiCL
open TwoDimentionalVector

structure Input where
deriving BEq, Repr
-- instance : ToString Input where toString s := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def maze_line := do
  let v ← many1 ((pchar '.').orElse fun _ ↦ pchar '#') <* eol
  return v.map (· == '#')

def maze := many1 maze_line >>= pure ∘ BoundedPlane.of2DMatrix

def parse : String → Option (Array (BoundedPlane Bool)) :=
  AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1

def solve (pls : Array (BoundedPlane Bool)) : Nat :=
  pls.map evaluate |> sum
  where
    evaluate (p : BoundedPlane Bool) : Nat :=
      0
     -- List.range p.shape.y.toNat ** List.range p.shape.y.toNat
     --  |>.map

end Part1

namespace Part2

def solve (_ : Array (BoundedPlane Bool)) : Nat := 0

end Part2

#eval (some #[3, 5]).map (·.shrink 1)
def solve := AocProblem.config 2023 13
  ((train toString dbgTrace K) ∘ (·.map (·.shrink 1)) ∘ parser.parse)
    -- y := parser.parse x ;
    -- dbgTrace s!"- parse result: {y.map (·.size)}" (fun _ ↦ y))
  Part1.solve
  Part2.solve

end Y2023.Day13
