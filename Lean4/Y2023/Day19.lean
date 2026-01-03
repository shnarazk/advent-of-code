module

public import Itertools
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2023.Day19

open CiCL Std
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
    | .Accept  => "Accept"
    | .Reject  => "Reject"
    | .Chain l => l

def Target.new : String → Target
  | "A" => Target.Accept
  | "R" => Target.Reject
  | s   => Target.Chain s

/-- A composition of var op num => action -/
structure Decl where
  label   : String
  op     : Operator
  num    : Nat
  action : Target
deriving BEq

instance : ToString Decl where
  toString r := s!"{r.label}{r.op}{r.num}:{r.action}"

/-- composition of label : rules* default -/
structure Rule where
  label : String
  rules : Array Decl
  default_rule : Target
deriving BEq

instance : ToString Rule where
  toString d := s!"{d.label}\{{d.rules},{d.default_rule}}"

abbrev Rules := HashMap String Rule

def makeInstruction (a : Array Rule) : Rules :=
  a.foldl (fun h d ↦ h.insert d.label d) HashMap.emptyWithCapacity

abbrev Setting := HashMap String Nat

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
  return Decl.mk var op num target
-- #eval AoCParser.parse prule "a<2006:qkq"
-- #eval AoCParser.parse prule "a<80:R"

def pdecl := do
  let label ← alphabets <* pchar '{'
  let rules ← separated prule (pchar ',') <* pchar ','
  let drule ← alphabets <* pchar '}'
  return Rule.mk label rules (Target.new drule)
-- #eval AoCParser.parse pdecl "rfg{s<537:gd,x>2440:R,A}"

def prating := do
  let name ← alphabets <* pchar '='
  let value ← number
  return (name, value)

def pratings := do
  let rs ← pchar '{' *> separated prating (pchar ',') <* pchar '}'
  let h := rs.foldl (fun h p ↦ HashMap.insert h (Prod.fst p) (Prod.snd p)) (HashMap.emptyWithCapacity : HashMap String Nat)
  return h
-- #eval AoCParser.parse (sepBy1 pratings eol) "{x=768,m=2655}\n{x=167,m=44}"

def parse : String → Option (Rules × Array Setting) := AoCParser.parse parser
 where
    parser := do
      let d ← separated pdecl eol <* eol
      let p ← eol *> separated pratings eol
      return (makeInstruction d, p)
-- #eval parse "rfg{s<537:gd,x>2440:R,A}\nqs{s>3448:A,lnx}\n\n{x=787}" |>.mapOr (·.fst) #[]
-- #eval parse "rfg{s<537:gd,lnx}\n\n{x=787,m=2655}" |>.mapOr (·.snd.map (·.toList)) #[]

end parser

namespace Part1

partial
def execute (rules : Rules) (setting : Setting) : Target → Option Nat
  | Target.Accept => some <| setting.values.foldl (· + ·) 0
  | Target.Reject => some 0
  | Target.Chain label =>
    if let some decl := rules.get? label then
      let result := decl.rules.foldl
          (fun state (decl : Decl) ↦ match state with
            | some _ => state
            | none =>
              (match setting.get? decl.label, decl.op with
                  | some val, .Lt => (val < decl.num : Bool)
                  | some val, .Gt => val > decl.num
                  | _, _ => (false : Bool))
              |>.then (K $ execute rules setting decl.action)
          )
          none
      if result.isSome then result else execute rules setting decl.default_rule
    else
      none

def solve (input : Rules × Array Setting) : Nat :=
  let (rules, settings) := input
  settings.map (execute rules · (Target.Chain "in")) |>.filterMap I |>.sum

end Part1

namespace Part2

partial
def collectPositives (rules : Rules) (range : Array (Nat × Nat)) : Target → Nat
  | Target.Accept => range.iter.map (fun (b, e) ↦ e - b + 1) |>.product
  | Target.Reject => 0
  | Target.Chain label =>
    if let some rule := rules.get? label then
      rule.rules.foldl
          (fun (total, (cond : Array (Nat × Nat))) rule ↦
            if let some (index, _) := #["x", "m", "a", "s"].iter.enumerate.find? (·.snd == rule.label) then
              match rule.op with
                | Operator.Lt =>
                    if rule.num ≤ cond[index]!.fst then
                      (total, cond)
                    else
                      (total +
                          collectPositives rules
                              (cond.set! index (cond[index]!.fst, cond[index]!.snd.min (rule.num - 1)))
                              rule.action,
                        cond.set! index (cond[index]!.fst.max rule.num, cond[index]!.snd))
                | Operator.Gt =>
                    if cond[index]!.snd ≤ rule.num then
                      (total, cond)
                    else
                      (total +
                          collectPositives rules
                              (cond.set! index (cond[index]!.fst.max (rule.num + 1), cond[index]!.snd) )
                              rule.action,
                        cond.set! index (cond[index]!.fst, cond[index]!.snd.min rule.num))
            else
              (total, range))
          (0, range)
        |> (fun (total, remains) ↦ total + collectPositives rules remains rule.default_rule)
    else
      0

def solve (input : Rules × Array Setting) : Nat :=
  collectPositives input.fst #[(1, 4000), (1, 4000), (1, 4000), (1, 4000)] (Target.Chain "in")

end Part2

public def solve := AocProblem.config 2023 19 parser.parse Part1.solve Part2.solve

end Y2023.Day19
