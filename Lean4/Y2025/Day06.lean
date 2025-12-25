module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2025.Day06
open Accumulation CiCL

inductive Op where
  | add
  | mul
deriving BEq, Hashable, Repr

instance : ToString Op where
  toString : Op → String
    | .add => "+"
    | .mul => "*"

structure Input where
  problems : Array (Array Nat)
  ops : Array Op
  data : String
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.problems} {s.ops} {s.data.length}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_values : Parser (Array Nat) := whitespaces? *> separated number whitespaces <* whitespaces?
def parse_part1 : Parser (Array (Array Nat)) := separated parse_values eol
def parse_op : Parser Op := do pchar '+' *> pure Op.add <|> pchar '*' *> pure Op.mul
def parse_ops : Parser (Array Op) := whitespaces? *> separated parse_op whitespaces

def parse (str : String) : Option Input := AoCParser.parse parser str
  where
    parser : Parser Input := do
      let problems ← parse_part1 <* eol
      let ops ← parse_ops
      pure <| Input.mk problems ops str

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

public def solve := AocProblem.config 2025 06 parser.parse Part1.solve Part2.solve

end Y2025.Day06
