import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser
-- import Mathlib.Data.List.BigOperators.Defs

namespace Day06

structure Race where
  race::
  time : Nat
  dist : Nat
deriving Repr

namespace parser
open Lean Parsec AoCParser

def numbers := sepBy1 number whitespaces

def ptime := pstring "Time:" *> whitespaces *> numbers
def pdist := pstring "Distance:" *> whitespaces *> numbers

-- #eval Parsec.run ptime "Time:     7 15  30"

def parser : Parsec (List Race) := do
  let t ← ptime <* eol
  let d ← pdist
  let m := List.transpose [t.toList, d.toList]
  return (List.map (fun r => Race.race (r.get! 0) (r.get! 1)) m)

def parse (data : String) :=
  match Parsec.run parser data with
  | Except.ok ret  => some ret
  | Except.error _ => none

-- #eval parse "Time: 7 15 30\nDistance: 9 40 200"

end parser

def evaluate₁ (race : Race) : Nat :=
  let ts := List.iota race.time
  (ts.filter (fun t => race.dist ≤ (race.time - t) * t)).length

def solve1 (data : String) : IO Unit := do
  match parser.parse data with
  | some races =>
    -- let _ ← List.mapM (fun r => IO.println s!"{r.time}, {r.dist}") races
    let vars := List.map evaluate₁ races
    IO.println s!"  part1: {vars.foldl Nat.mul 0}"
  | _ =>
    IO.println s!"  part1: parse error"
  return ()

def solve2_line (_line : String) : Nat :=
  0

def solve2 (data : String) : IO Unit := do
  let x := (data.split (. == '\n')).map (fun l =>
    List.foldl (fun n d => n * 10 + d.toNat - '0'.toNat) 0 (l.toList.filter Char.isDigit))
  let res := evaluate₁ ({ time := x.get! 0, dist := x.get! 1} : Race)
  IO.println s!"  part2: {res}"

end Day06

def day06 (ext : Option String): IO Unit := do
  let data ← dataOf 2023 6 ext
  Day06.solve1 data
  Day06.solve2 data
