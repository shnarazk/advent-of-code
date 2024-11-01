import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
-- import «AoC».Rect64

namespace Y2023.Day19

open Accumulation CiCL

inductive Operator where | Lt | Gt deriving BEq

instance : ToString Operator where
  toString : Operator → String | .Lt => "<" | .Gt => ">"

structure Rule where
  var : String
  op : Operator
  num : Nat
  action : String
deriving BEq

instance : ToString Rule where
  toString r := s!"{r.var}{r.op}{r.num}:{r.action}"

structure Decl where
  label : String
  rules : List Rule
  default_rule : String
deriving BEq

instance : ToString Decl where
  toString d := s!"{d.label}\{{d.rules},{d.default_rule}}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def prule := do
  let var ← alphabets
  let op ← pchar '<' <|> pchar '>'
  let num ← number <* pchar ':'
  let conc ← pstring "R" <|> pstring "A" <|> alphabets
  return Rule.mk var (if op == '<' then Operator.Lt else Operator.Gt) num conc

-- #eval AoCParser.parse prule "a<2006:qkq"

def parse : String → Option (Array Decl) := AoCParser.parse parser
  where
    parser : Parser (Array Decl):= return #[Decl.mk "aa" [] "A"]

-- #eval parse "a<2006:qkq"

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 19
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day19
