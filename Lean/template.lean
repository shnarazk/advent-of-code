import Batteries
import Std
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y20XX.DayXX

open Std Accumulation CoP

def year : Nat := 2024
def day : Nat := 1

structure Input where
deriving BEq, Repr
-- instance : ToString Input where toString s := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := return Input.mk

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

protected def solve (alt : Option String): IO Answers := do
  if let some d := parser.parse (← dataOf year day alt)
  then return (s!"{Part1.solve d}", s!"{Part2.solve d}")
  else return ("parse error", "")

end Y20XX.DayXX
