import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2023.Day19

open Accumulation CiCL Std
abbrev HashMap := Std.HashMap

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
open Std.HashMap

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

def prating := do
  let name ← alphabets <* pchar '='
  let value ← number
  return (name, value)

def pratings := do
  let rs ← pchar '{' *> sepBy1 prating (pchar ',') <* pchar '}'
  let h := rs.foldl (fun h p ↦ HashMap.insert h (Prod.fst p) (Prod.snd p)) (HashMap.empty : HashMap String Nat)
  return h
-- #eval AoCParser.parse (sepBy1 pratings eol) "{x=768,m=2655}\n{x=167,m=44}"

def parse : String → Option (HashMap String Decl × Array (HashMap String Nat)) := AoCParser.parse parser
 where
    parser := do
      let d ← sepBy1 pdecl eol <* eol
      let p ← eol *> sepBy1 pratings eol
      return (makeInstruction d, p)
-- #eval parse "rfg{s<537:gd,x>2440:R,A}\nqs{s>3448:A,lnx}\n\n{x=787}" |>.mapOr (·.fst) #[]
-- #eval parse "rfg{s<537:gd,lnx}\n\n{x=787,m=2655}" |>.mapOr (·.snd.map (·.toList)) #[]

end parser

namespace Part1

def solve (input : HashMap String Decl × Array (HashMap String Nat)) : Nat :=
  let (decls, ratings) := input
  if let some label_in := decls.get? "in" then
    dbg s!"got: {label_in}" 0
  else
    dbg s!"{decls |>.toList}, rating{ratings.map (·.toList)}" 0

end Part1

namespace Part2

def solve (_input : HashMap String Decl × Array (HashMap String Nat)) : Nat :=
  0

end Part2

def solve := AocProblem.config 2023 19 parser.parse Part1.solve Part2.solve

end Y2023.Day19
