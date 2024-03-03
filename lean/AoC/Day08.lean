import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day08
open Std

structure Puzzle where
  new ::
  path     : List Char
  branches : Std.HashMap String (String × String)

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
  let hash := Array.foldl (fun h (b : String × String × String) =>
    HashMap.insert h b.fst b.snd) (HashMap.empty) branches
  return Puzzle.new path.toList hash

end parser

partial def trace : Puzzle → Nat → String → Nat
  | _, step, "ZZZ" => step
  | puzzle, step, pos =>
    let (left, right) := puzzle.branches.find! pos
    let dir := puzzle.path[step % puzzle.path.length]!
    trace puzzle (step + 1) $ if dir == 'L' then left else right

def solve1 (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some p => IO.println s!"  part1: {trace p 0 "AAA"}"
  return ()

def solve2_line (_line : String) : Nat := 0

-- #eval solve2_line ""

def solve2 (_data : String) : IO Unit := do
  IO.println s!"  part2: -"
  return ()

end Day08

def day08 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 8 ext
  pure data >>= Day08.solve1
  pure data >>= Day08.solve2
