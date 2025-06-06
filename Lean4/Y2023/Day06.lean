import «AoC».Basic
import «AoC».Parser

namespace Y2023.Day06
open Accumulation

structure Race where
  new::
  time : Nat
  dist : Nat
deriving BEq, Repr

namespace Race

private def qualify (r : Race) (t : Nat) : Ordering := compare ((r.time - t) * t) r.dist

private def seek (r : Race) (span : Nat) (i j : Nat) (inc : Bool) : Nat :=
  if span = 0 then if inc then j else i
  else
    let m := (i + j) / 2
    match qualify r m with
    | Ordering.lt => if inc then seek r (span / 2) m j inc else seek r (span / 2) i m inc
    | Ordering.eq => m
    | Ordering.gt => if inc then seek r (span / 2) i m inc else seek r (span / 2) m j inc

def evaluate (r : Race) : Nat :=
  let m := r.time / 2
  let i := seek r m 0 m true
  let j := seek r m m r.time false
  j - i + 1

end Race

namespace parser

open Lean Parser AoCParser
open Std.Internal.Parsec.String

def numbers := sepBy1 number whitespaces
def ptime := pstring "Time:" *> whitespaces *> numbers
def pdist := pstring "Distance:" *> whitespaces *> numbers

-- #eval Parsec.run ptime "Time:     7 15  30"

def parser : Parser (List Race) := do
  let t ← ptime <* eol
  let d ← pdist
  let m := List.transpose [t.toList, d.toList]
  return (List.map (fun r => Race.new r[0]! r[1]!) m)

def parse (data : String) :=
  match Parser.run parser data with
  | Except.ok ret  => some ret
  | Except.error _ => none

-- #eval parse "Time: 7 15 30\nDistance: 9 40 200"

end parser

def Part1.solve (data : String) : String :=
  if let some races := parser.parse data then
    s!"{races.map Race.evaluate|> product}"
  else
    "parse error"

def Part2.solve (data : String) : Nat :=
  let x := (data.split (. == '\n')).map (fun l =>
      List.foldl
          (fun n d => n * 10 + d.toNat - '0'.toNat)
          0
          (l.toList.filter Char.isDigit))
  let r := Race.new x[0]! x[1]!
  r.evaluate

def solve := AocProblem.config 2023 6 some Part1.solve Part2.solve

end Y2023.Day06
