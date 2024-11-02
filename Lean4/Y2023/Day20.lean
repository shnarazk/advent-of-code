import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
-- import «AoC».Rect64

namespace Y2023.Day20

open Accumulation CiCL

structure Input where
deriving BEq, Repr
instance : ToString Input where toString _ := s!""

inductive Module where
  | Broadcaster
  | FlipFlop (label : String)
  | Conjunction (label : String)
deriving BEq

instance : ToString Module where
  toString : Module → String
    | Module.Broadcaster => "Broadcaster"
    | Module.FlipFlop s => s!"FF:{s}"
    | Module.Conjunction s => s!"Con:{s}"
-- #eval Module.FlipFlop "ab"
-- #eval Module.Conjunction "ab"

inductive Link where | To | Low | High
deriving BEq

instance : ToString Link where
  toString : Link → String
    | Link.To   => "->"
    | Link.Low  => "-low->"
    | Link.High => "-high->"

structure Rule where
  module : Module
  link   : Link
  outputs : Array String
deriving BEq

instance : ToString Rule where
  toString r := s!"{r.module} {r.link} {r.outputs}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def pmodule := pbroadcaster <|> pflipflop <|> pconjunction
  where
    pbroadcaster := pstring "broadcaster"  *> return Module.Broadcaster
    pflipflop    := pchar '%' *> alphabets >>= pure ∘ Module.FlipFlop
    pconjunction  := pchar '&' *> alphabets >>= pure ∘ Module.Conjunction
-- #eval AoCParser.parse pmodule "broadcaster"
-- #eval AoCParser.parse pmodule "%a"
-- #eval AoCParser.parse pmodule "&inv"

def plink := plink_ <|> plinkL <|> plinkH
  where
    plink_ := pstring "->"      *> return Link.To
    plinkL := pstring "-low->"  *> return Link.Low
    plinkH := pstring "-high->" *> return Link.High
-- #eval AoCParser.parse plink "->"
-- #eval AoCParser.parse plink "-high->"

def poutputs := sepBy1 alphabets (pstring ", ")
-- #eval AoCParser.parse outputs "a"
-- #eval AoCParser.parse outputs "a, b, c"

def pline := do
  let m ← pmodule <* whitespaces
  let l ← plink <* whitespaces
  let o ← poutputs
  return Rule.mk m l o
-- #check pline
-- #eval AoCParser.parse pline "%a -> inv, con"

def parse : String → Option (Array Rule) := AoCParser.parse parser
  where
    parser := sepBy1 pline eol
-- #eval parse "%a -> inv, con\n&inv -> b"

end parser

namespace Part1

def solve (_ : Array Rule) : Nat := 0

end Part1

namespace Part2

def solve (_ : Array Rule) : Nat := 0

end Part2

def solve := AocProblem.config 2023 20
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day20
