module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2025.Day07

open Std Accumulation

structure Input where
  splitters : List (List Nat)
  start : Nat
deriving BEq

instance : ToString Input where toString s := s!"{s.splitters}, {s.start}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_nmemonic := pchar '.' <|> pchar '^' <|> pchar 'S'
def parse_line := repeated parse_nmemonic
def parse_input := separated parse_line eol

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
    let grid ← parse_input
    let mut start := 0
    let mut splitters : List (List Nat) := []
    for l in grid do
      let mut sps := []
      for (j, ch) in l.enumerate do
        if ch == 'S' then start := j
        if ch == '^' then sps := sps.insert j
      if !sps.isEmpty then splitters := splitters.concat sps
    pure <| Input.mk splitters start

end parser

namespace Part1

def solve (input : Input) : Nat := Id.run do
  let mut numSplits := 0
  let mut pos : HashSet Nat := HashSet.emptyWithCapacity 100
  pos := pos.insert input.start
  for line in input.splitters do
    let mut next : HashSet Nat := HashSet.emptyWithCapacity 10
    for p in pos do
      if line.contains p then
        numSplits := numSplits + 1
        next := next.insert (p - 1)
        next := next.insert (p + 1)
      else
        next := next.insert p
    pos := next
  numSplits

end Part1

namespace Part2

def solve (input : Input) : Nat := Id.run do
  0

end Part2

public def solve := AocProblem.config 2025 07 parser.parse Part1.solve Part2.solve

end Y2025.Day07
