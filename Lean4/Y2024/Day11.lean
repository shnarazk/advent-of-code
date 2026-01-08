module

public import Itertools
public import WinnowParsers
public import «AoC».Basic

namespace Y2024.Day11

open Std

structure Input where
  line: Array Nat
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"

def digits (n : Nat) : List Nat :=
  if n == 0 then
    []
  else
    digits (n / 10) ++ [n % 10]
decreasing_by
  expose_names
  simp at h
  refine Nat.div_lt_self ?_ ?_
  · exact Nat.ne_zero_iff_zero_lt.mp h
  · exact Nat.one_lt_succ_succ 8

#guard digits 12 == [1, 2]
#guard digits 2 == [2]
#guard digits 0 == []
#guard digits 3568 == [3, 5, 6, 8]

def undigits (l : List Nat) : Nat := l.foldl (· * 10 + ·) 0

#guard undigits [1, 2, 5, 0] == 1250
#guard undigits [5] == 5

def dividable (n : Nat) : Option (Nat × Nat) :=
  let l := digits n
  if l.length % 2 == 0 then
    some (l.take (l.length / 2) |> undigits, l.drop (l.length / 2) |> undigits)
  else
    none

#guard dividable 1234 == some (12, 34)
#guard dividable 14 == some (1, 4)
#guard dividable 148 == none

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> separated number (pchar ' ')

end parser

namespace Part1

partial
def count_stones (max_depth depth n : Nat) : Nat :=
  if max_depth == depth then
    1
  else
    if n == 0 then
      count_stones max_depth (depth + 1) 1
    else
      match dividable n with
      | some (a, b) => (count_stones max_depth (depth + 1) a) + (count_stones max_depth (depth + 1) b)
      | _ => count_stones max_depth (depth + 1) (2024 * n)

def solve (input : Input) : Nat := input.line.iter.map (fun n ↦ count_stones 25 0 n) |>.sum

end Part1

namespace Part2

abbrev Memo := HashMap (Nat × Nat) Nat

partial
def count_stones (memo : Memo) (max_depth depth n : Nat) : Memo × Nat := Id.run do
  if let some c := memo.get? (depth, n) then
    return (memo, c)
  if max_depth == depth then
    return (memo, 1)
  else
    if n == 0 then
      let (memo', c) := count_stones memo max_depth (depth + 1) 1
      return (memo'.insert (depth, n) c, c)
    else
      match dividable n with
      | some (a, b) =>
        let (memo', c1) := count_stones memo max_depth (depth + 1) a
        let (memo'', c2) := count_stones memo' max_depth (depth + 1) b
        return (memo''.insert (depth, n) (c1 + c2), c1 + c2)
      | _ =>
        let (memo', c) := count_stones memo max_depth (depth + 1) (2024 * n)
        return (memo'.insert (depth, n) c, c)

def solve (input : Input) : Nat := Id.run do
  let mut memo : Memo := HashMap.emptyWithCapacity 100
  let mut count := 0
  for n in input.line do
    let (memo', c) := count_stones memo 75 0 n
    count := count + c
    memo := memo'
  count

end Part2

public def solve := AocProblem.config 2024 11 parser.parse Part1.solve Part2.solve

end Y2024.Day11
