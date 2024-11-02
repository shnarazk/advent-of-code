import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2023.Day19

open Accumulation CiCL Std

inductive Operator where | Lt | Gt deriving BEq

instance : ToString Operator where
  toString : Operator → String | .Lt => "<" | .Gt => ">"

inductive Target where
  | Accept
  | Reject
  | Chain (s : String)
deriving BEq

instance : ToString Target where
  toString : Target → String
    | .Accept  => "A"
    | .Reject  => "R"
    | .Chain l => l

def Target.new : String → Target
  | "A" => Target.Accept
  | "!" => Target.Reject
  | s   => Target.Chain s

structure Rule where
  var    : String
  op     : Operator
  num    : Nat
  action : Target
deriving BEq

instance : ToString Rule where
  toString r := s!"{r.var}{r.op}{r.num}:{r.action}"

structure Decl where
  label : String
  rules : Array Rule
  default_rule : Target
deriving BEq

instance : ToString Decl where
  toString d := s!"{d.label}\{{d.rules},{d.default_rule}}"

def makeInstruction (a : Array Decl) : (HashMap String Decl) :=
  a.foldl (fun h d ↦ h.insert d.label d) HashMap.empty

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def prule := do
  let var ← alphabets
  let op' ← pchar '<' <|> pchar '>'
  let num ← number <* pchar ':'
  let conc ← pstring "R" <|> pstring "A" <|> alphabets
  let op := if op' == '<' then Operator.Lt else Operator.Gt
  let target := Target.new conc
  return Rule.mk var op num target
-- #eval AoCParser.parse prule "a<2006:qkq"

def pdecl := do
  let label ← alphabets <* pchar '{'
  let rules ← sepBy1 prule (pchar ',') <* pchar ','
  let drule ← alphabets <* pchar '}'
  return Decl.mk label rules (Target.new drule)
-- #eval AoCParser.parse pdecl "rfg{s<537:gd,x>2440:R,A}"

def parse : String → Option (Array Decl) := AoCParser.parse parser
  where
    parser : Parser (Array Decl):= sepBy1 pdecl eol
-- #eval parse "rfg{s<537:gd,x>2440:R,A}\nqs{s>3448:A,lnx}"

end parser

namespace Part1

def solve (a : Array Decl) : Nat :=
 dbg s!"{makeInstruction a |>.toList}" 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 19
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day19
