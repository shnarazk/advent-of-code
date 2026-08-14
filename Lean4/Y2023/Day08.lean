module

public import WinnowParsers
public import «AoC».Basic

namespace Y2023.Day08

open Std

structure Puzzle where
  path     : List Char
  branches : HashMap String (String × String)

namespace parser

open WinnowParsers
open Std.Internal.Parsec.String

def pbranch := do
  let label ← alphabets <* whitespaces <* pchar '=' <* whitespaces
  let left  ← pchar '(' *> alphabets <* pchar ',' <* whitespaces
  let right ← alphabets <* pchar ')'
  return (label, (left, right))

def parse := AoCParser.parse parser
  where parser := do
    let path ← alphabets <* eol <* eol
    let branches ← separated pbranch eol
    let hash := branches.foldl
      (fun h (b : String × String × String) => HashMap.insert h b.fst b.snd)
      HashMap.emptyWithCapacity
    return Puzzle.mk path.toList hash

end parser

def trace₁ : Puzzle → Nat → Nat → String → Nat
  | _     ,      _,  step, "ZZZ" => step
  | _     ,       0, step,     _ => step
  | puzzle, lim + 1, step,   pos =>
    let (left, right) := puzzle.branches.get! pos
    let dir := puzzle.path[step % puzzle.path.length]!
    trace₁ puzzle lim (step + 1) <| if dir == 'L' then left else right

def Part1.solve (p : Puzzle) : Nat :=
  trace₁ p (Nat.lcm p.path.length p.branches.size) 0 "AAA"

def trace₂ (puzzle : Puzzle) (limit : Nat) (step : Nat) (pos : String) : Nat :=
  match limit with
  | 0 => 0
  | lim + 1 =>
    if pos.endsWith "Z" then
      step
    else
      let (left, right) := puzzle.branches.get! pos
      let dir := puzzle.path[step % puzzle.path.length]!
      trace₂ puzzle lim (step + 1) <| if dir == 'L' then left else right

#guard Nat.lcm 1 9 == 9

def Part2.solve (p : Puzzle) : Nat :=
  let limit := Nat.lcm p.path.length p.branches.size
  p.branches.toList.filter (String.endsWith ·.fst "A")
    |>.map (trace₂ p limit 0 ·.fst)
    |>.foldl Nat.lcm 1

public def solve := AocProblem.config 2023 8 parser.parse Part1.solve Part2.solve

end Y2023.Day08
