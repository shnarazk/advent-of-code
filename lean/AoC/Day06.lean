import Std
import «AoC».Basic
import «AoC».Parser
import Lean.Data.Parsec

namespace Day06

structure Race where
  time : Array Nat
  dist : Array Nat
deriving Repr

#eval ({ time := #[3, 3, 1], dist := #[1, 2, 3] } : Race).time

namespace parser
open Lean Parsec

def numbers := sepBy1 number whitespaces

def ptime := pstring "Time:" *> whitespaces *> numbers
def pdist := pstring "Distance:" *> whitespaces *> numbers

#eval Parsec.run ptime "Time:     7 15  30"

def parser : Parsec Race := do
  let t ← ptime <* eol
  let d ← pdist
  return ({ time := t, dist := d } : Race)

def parse (data : String) :=
  match Parsec.run parser data with
  | Except.ok ret  => some ret
  | Except.error _ => none

#eval parse "Time: 7 15 30\nDistance: 9 40 200"

end parser

def solve1 (data : String) : IO Unit := do
  match parser.parse data with
  | some x =>
    IO.println s!" part1: not yet implemented {x.time}"
  | _ =>
    IO.println s!" part1: parse error"
  return ()

def solve2_line (_line : String) : Nat :=
  0

def solve2 (data : String) : IO Unit := do
  match parser.parse data with
  | some _ =>
    IO.println s!" part2: not yet implemented"
  | _ =>
      IO.println s!"error"
  return ()

end Day06

def day06 : IO Unit := do
  let data ← dataOf 2023 6
  pure data >>= Day06.solve1
  pure data >>= Day06.solve2
