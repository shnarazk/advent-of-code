import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day06

structure Race where
  race::
  time : Nat
  dist : Nat
deriving Repr

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

namespace Part1

def solve (data : String) : IO Unit := do
  match parser.parse data with
  | some races =>
    let vars := List.map Race.evaluate races
    IO.println s!"  part1: {vars.foldl Nat.mul 1}"
  | _ =>
    IO.println s!"  part1: parse error"
  return ()

end Part1

namespace Part2

def solve (data : String) : IO Unit := do
  let x := (data.split (. == '\n')).map (fun l =>
    List.foldl (fun n d => n * 10 + d.toNat - '0'.toNat) 0 (l.toList.filter Char.isDigit))
  let r := Race.race (x.get! 0) (x.get! 1)
  IO.println s!"  part2: {r.evaluate}"

end Part2

end Day06

def day06 (ext : Option String): IO Unit := do
  let data ← dataOf 2023 6 ext
  Day06.Part1.solve data
  Day06.Part2.solve data
