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

#eval [1, 2, 5].tail
#eval List.drop 2 [1, 2, 5]
#eval compare 3 5 == Ordering.lt

private partial def match_sequence
    (hash   : HashMap (String × Nat) Nat)
    (target : List Char)
    (rule   : List Nat)
    : (HashMap (String × Nat) Nat) × Nat :=
  -- check memorized value first
  let key := (target.foldl (fun s e => s.push e) "", rule.length)
  match hash.find? key with
  | some combinations => (hash, combinations)
  | none =>
    let key := (target.foldl (fun s e => s.push e) "", rule.length)
    match target with
    | []      => let x := if rule == [] then 1 else 0 ;  (hash.insert key x, x)
    | t :: t' =>
      match rule with
      | []      => let x := if target.all (· != '#') then 1 else 0 ; (hash.insert key x, x)
      | r :: r' =>
        -- index boundary check
        if target.length < rule.length then (hash.insert key 0, 0) else
          match t with
          | '.' => match_sequence hash t' rule
          | '#' =>
            let chank_len : Nat := target.findIdx (· != t)
            match compare r chank_len with
            | Ordering.lt => (hash.insert key 0, 0)
            | Ordering.eq => match_sequence hash (List.drop r t') r'
            | Ordering.gt =>
              if target.length < r
              then (hash.insert key 0, 0)
              else
                if (List.range r).all (target[·]! != '.') && (r == target.length || target[r]! != '#')
                then match_sequence hash (List.drop r t') r'
                else (hash.insert key 0, 0)
          | '?' =>
            let (_, m) := match_sequence hash ('.' :: t') rule
            let (_, n) := match_sequence hash ('#' :: t') rule
            (hash, m + n)
          | _   => panic "impossible"

-- #eval match_sequence HashMap.empty "..".toList [] |>.snd
-- #eval match_sequence HashMap.empty "##".toList [2] |>.snd
-- #eval match_sequence HashMap.empty "#.#".toList [1,1] |>.snd
#eval match_sequence HashMap.empty "?".toList [1] |>.snd
#eval match_sequence HashMap.empty "??".toList [2] |>.snd
#eval match_sequence HashMap.empty "#?".toList [2] |>.snd
#eval match_sequence HashMap.empty "?#?".toList [2] |>.snd
#eval match_sequence HashMap.empty "#?#?".toList [2] |>.snd
#eval match_sequence HashMap.empty "#?#?".toList [3] |>.snd
#eval match_sequence HashMap.empty "#?#?".toList [4] |>.snd
#eval match_sequence HashMap.empty "?#?#?".toList [3] |>.snd

def evaluate (conf : Data) : Nat :=
  match_sequence (HashMap.empty : HashMap (String × Nat) Nat) conf.pattern.toList conf.rule.toList
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