import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

abbrev Vec2 := (Int × Int)

namespace Y2024.Day06

open Accumulation CiCL

inductive Dir
  | N
  | E
  | S
  | W
deriving BEq, Repr

namespace Dir
def turn : Dir -> Dir
  | Dir.N => Dir.E
  | Dir.E => Dir.S
  | Dir.S => Dir.W
  | Dir.W => Dir.N
#eval Dir.E.turn

end Dir

structure Input where
  line : Array (Array Char)
  obstruction : Std.HashSet Vec2
  guardPos : Vec2
  guardDir : Dir
  size: Vec2
deriving BEq, Repr

instance : ToString Input where toString self := s!"{self.obstruction.toList}"

namespace Input

def turn (self : Input) : Input :=
  { self with guardDir := self.guardDir.turn }

def includes (self : Input) (pos : Vec2) : Option Vec2 :=
  if 0 <= pos.1 && pos.1 < self.size.1 && 0 <= pos.2 && self.size.2 < pos.2
    then some pos
    else none

end Input

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseLine := do
  many1 (pchar '.' <|> pchar '#' <|> pchar '^')
-- #eval AoCParser.parse parseLine "^..#"

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← many1 (parseLine <* eol)
      let h := v.enum.foldl
        (fun h (i, l) ↦ l.enum.foldl
          (fun h (j, c) ↦ if c == '#' then h.insert ((i : Int), (j : Int)) else h)
          h)
        Std.HashSet.empty
      let p := v.enum.flatMap
          (fun (i, l) ↦ l.enum.flatMap (fun (j, c) ↦ if c == '^' then #[(i, j)] else #[]))
          |>.get! 0
      let size := ((v.size : Int), (v[0]!.size : Int))
      return Input.mk v h ((p.1 : Int), (p.2 : Int)) Dir.N size

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 06
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day06
