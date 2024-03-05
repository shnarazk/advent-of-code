import Std
import Lean.Data.Parsec
import Mathlib.Data.Matrix.Basic
import «AoC».Basic
import «AoC».Parser

namespace Day10
open Std

structure Data where
  new ::
  grid : Array (Array Char)
deriving Repr

-- def Data.of (self : Data) (y : Nat) (x : Nat) : Char := (self.grid[y]!)[x]!
def Data.at (self : Data) : Matrix Nat Nat Char := fun y x => (self.grid[y]!)[x]!

#eval (Data.new #[#['0', '1'], #['2', '3']]).at 0 0
#eval (Data.new #[#['0', '1'], #['2', '3']]).at 1 1

inductive Circuit where
  | h : Circuit
  | l : Circuit
  | j : Circuit
  | k : Circuit
  | f : Circuit
  | S : Circuit

def dest (pre : Nat × Nat) (c : Circuit) (pos : Nat × Nat) : Nat × Nat :=
  let dy := pos.fst - pre.fst
  let dx := pos.snd - pre.snd
  match c with
  | .h /- - -/ => (pos.fst      , pos.snd + dx)
  | .l /- L -/ => (pos.fst + dy , pos.snd)
  | .j /- J -/ => (pos.fst + dx , pos.snd)
  | .k /- 7 -/ => (pos.fst      , pos.snd)
  | .f /- F -/ => (pos.fst      , pos.snd)
  | .S /- . -/ => (pos.fst      , pos.snd)

#eval #['a', 'b'].toList.toString
#eval #["aa", "bb"].foldl (fun x y => x ++ y) ""

 instance : ToString Data where
   toString self := self.grid.map (· |>.foldl String.push ""|>.append "\n")
      |>.foldl String.append ""

namespace parser
open Lean.Parsec AoCParser

def cell := pchar '|'
    <|> pchar '-'
    <|> pchar 'L'
    <|> pchar 'J'
    <|> pchar '7'
    <|> pchar 'F'
    <|> pchar '.'
    <|> pchar 'S'

def parser := do
  let cs ← many (many cell <* eol)
  return (Data.new cs)

end parser

namespace part1
def solve (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some d => IO.println s!"  part1: {d}"
  return ()

end part1

namespace part2

def solve (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part2: parse error"
  | some d => IO.println s!"  part2: {d}"
  return ()

end part2

end Day10

def day10 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 10 ext
  Day10.part1.solve data
  Day10.part2.solve data
