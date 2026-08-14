module

public import Itertools
public meta import Itertools
public import WinnowParsers
public meta import WinnowParsers
public import «AoC».Basic
public meta import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec

namespace Y2024.Day14

open Std
open Dim2

/-- The input data. -/
structure Input where
  pos : Vec₂
  vec : Vec₂
deriving BEq, Hashable, Repr

instance : ToString Input where
  toString s := s!"{s.pos}:{s.vec}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseInput : Parser Input := do
  let p1 ← pstring "p=" *> number_signed
  let p2 ← pstring "," *> number_signed
  let v1 ← pstring " v=" *> number_signed
  let v2 ← pstring "," *> number_signed
  pure <| Input.mk (p1, p2) (v1, v2)

#guard AoCParser.parse parseInput "p=0,4 v=3,-1" == some (Input.mk (0, 4) (3, -1))

def parse : String → Option (Array Input) := AoCParser.parse parser
  where
    parser : Parser (Array Input) := separated parseInput eol

end parser

namespace Part1

def solve (_ : Array Input) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : Array Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2024 14
  ((CiCL.T dbg (fun data ↦ s!"got {data.unwrapOr #[] |>.size} elements")) ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day14
