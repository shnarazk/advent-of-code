import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day08
open Std

structure Puzzle where
  new ::
  path     : List Char
  branches : HashMap String (String × String)

namespace parser
open Lean.Parsec AoCParser

def ppath := alphabets
def pbranch := do
  let label ← alphabets <* whitespaces <* pchar '=' <* whitespaces
  let left  ← pchar '(' *> alphabets <* pchar ',' <* whitespaces
  let right ← alphabets <* pchar ')'
  return (label, (left, right))

def parser := do
  let path ← ppath <* eol <* eol
  let branches  ← sepBy1 pbranch eol
  let hash := branches.foldl
    (fun h (b : String × String × String) => HashMap.insert h b.fst b.snd)
    HashMap.empty
  return Puzzle.new path.toList hash

end parser

partial def trace₁ : Puzzle → Nat → String → Nat
  | _     , step, "ZZZ" => step
  | puzzle, step, pos   =>
    let (left, right) := puzzle.branches.find! pos
    let dir := puzzle.path[step % puzzle.path.length]!
    trace₁ puzzle (step + 1) <| if dir == 'L' then left else right

def solve1 (data : String) : IO Unit := do
  if let some p := AoCParser.parse parser.parser data then
    IO.println s!"  part1: {trace₁ p 0 "AAA"}"

partial def trace₂ (puzzle : Puzzle) (step : Nat) (pos : String) : Nat :=
  if pos.endsWith "Z"
  then step
  else
    let (left, right) := puzzle.branches.find! pos
    let dir := puzzle.path[step % puzzle.path.length]!
    trace₂ puzzle (step + 1) <| if dir == 'L' then left else right

-- #eval Nat.lcm 1 9

def analyze (p : Puzzle) : Nat :=
  p.branches.toList.filter (String.endsWith ·.fst "A")
    |>.map (trace₂ p 0 ·.fst)
    |>.foldl Nat.lcm 1

def solve2 (data : String) : IO Unit := do
  if let some p := AoCParser.parse parser.parser data then
    IO.println s!"  part2: {analyze p}"

end Day08

def day08 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 8 ext
  Day08.solve1 data
  Day08.solve2 data
