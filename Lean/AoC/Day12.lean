import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Day12
open Std Accumulation CoP

structure Data where
  new ::
  pattern : Array Char
  rule    : Array Nat
deriving Repr

instance : ToString Data where
  toString s := s!"\"{String.intercalate "" (Array.map toString s.pattern).toList}\" :: {s.rule}\n"

namespace parser
open Lean.Parsec AoCParser

def line_parser := do
  let pattern ← many1 (pchar '.' <|> pchar '#' <|> pchar '?') <* whitespaces
  let rule    ← sepBy1 number (pchar ',')
  return Data.new pattern rule

def parser := sepBy1 line_parser eol

end parser

namespace part1

private def match_sequence
    (hash   : HashMap (String × Nat) Nat)
    (target : Array Char)
    (rule   : Array Nat)
    : (HashMap (String × Nat) Nat) × Nat :=
  match target, rule with
  | #[], #[] => (hash, 1)
  | _  , #[] => (hash, if target.all (· != '#') then 1 else 0)
  | #[],   _ => (hash, 0)
  |   _,   _ =>
    if target.size < sum rule then (hash, 0) else
      let _start := target[0]!
      let _ends_at := target.enumerate.find? (fun (_i, x) => x == ' ')
      (hash, 0)

/--
memorizing wrapper
-/
private def match_sequence'
    (hash   : HashMap (String × Nat) Nat)
    (target : Array Char)
    (rule   : Array Nat)
    : (HashMap (String × Nat) Nat) × Nat :=
  let key := (target.foldl (fun s e => s.push e) "", rule.size)
  match hash.find? key with
  | some combinations => (hash, combinations)
  | none =>
    let (h', n) := match_sequence hash target rule
    (h'.insert key n, n)

def evaluate (conf : Data) : Nat :=
  match_sequence (HashMap.empty : HashMap (String × Nat) Nat) conf.pattern conf.rule
  |>.snd

def solve (data : String) : IO Unit := do
  if let some cs := AoCParser.parse parser.parser data then
    IO.println s!"  part1: {sum $ Array.map evaluate cs}"

end part1

namespace part2

def evaluate (_conf : Data) : Nat := 0

-- #eval evaluate ""

def solve (data : String) : IO Unit := do
  if let some cs := AoCParser.parse parser.parser data then
    IO.println s!"  part2: {sum $ Array.map evaluate cs}"

end part2

end Day12

def day12 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 12 ext
  Day12.part1.solve data
  Day12.part2.solve data
