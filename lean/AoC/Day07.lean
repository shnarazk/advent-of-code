import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day07

structure Hand where
  hand ::
  cards : Array Char
  bid   : Nat
deriving Inhabited, Repr

namespace parser
open Lean Parsec AoCParser

def card := digit <|> pchar 'A' <|> pchar 'K' <|> pchar 'Q' <|> pchar 'J' <|> pchar 'T'

def cards := many1 card <* whitespaces

def line := do
  let c ← cards
  let b ← number
  return Hand.hand c b

def parser := sepBy1 line eol

end parser

def solve1_line (_line : String) : Nat := 0


def solve1 (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some d => IO.println s!"  part1: {d.size}"
  return ()

def solve2_line (_line : String) : Nat := 0

def solve2 (_lines : String) : IO Unit := do
  let sum := 0
  IO.println s!"  part2: {sum}"
  return ()

end Day07

def day07 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 7 ext
  pure data >>= Day07.solve1
  pure data >>= Day07.solve2
