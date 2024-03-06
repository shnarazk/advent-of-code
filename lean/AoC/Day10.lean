import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day10
open Std

inductive Circuit where
  | v : Circuit
  | h : Circuit
  | l : Circuit
  | j : Circuit
  | k : Circuit
  | f : Circuit
  | S : Circuit
  | x : Circuit
deriving BEq, Repr

instance : ToString Circuit where
  toString s :=
  match s with
  | .v => "|"
  | .h => "-"
  | .l => "L" 
  | .j => "J" 
  | .k => "7" 
  | .f => "F" 
  | .S => "S" 
  | _  => " "
    
def Circuit.ofChar (c : Char) : Circuit :=
  match c with
  | '|' => .v
  | '-' => .h
  | 'L' => .l
  | 'J' => .j
  | '7' => .k
  | 'F' => .f
  | 'S' => .S
  |  _  => .x

#eval (Circuit.ofChar 'f') |> toString

structure Data where
  new ::
  grid : Array (Array Circuit)
deriving BEq, Repr

#eval (none : Option Nat).map (fun _ => 3)

def Data.at (self : Data) (pos : Nat × Nat) : Option Circuit :=
  (self.grid[pos.fst]?) >>= (·[pos.snd]?)

partial def Data.dest (c : Data) (pre : Nat × Nat) (pos : Nat × Nat) : (Nat × Nat) × (Nat × Nat) :=
  let dy := pos.fst - pre.fst
  let dx := pos.snd - pre.snd
  match c.at pos with
  | some .v /- - -/ => (pos, (pos.fst + dy , pos.snd     ))
  | some .h /- - -/ => (pos, (pos.fst      , pos.snd + dx))
  | some .l /- L -/ => (pos, (pos.fst      , pos.snd + dy))
  | some .j /- J -/ => (pos, (pos.fst - dx , pos.snd     ))
  | some .k /- 7 -/ => (pos, (pos.fst + dx , pos.snd     ))
  | some .f /- F -/ => (pos, (pos.fst      , pos.snd - dy))
  | _ /- . -/ => (pos, pos)

#eval #['a', 'b'].toList.toString
#eval #["aa", "bb"].foldl (fun x y => x ++ y) ""

 instance : ToString Data where
   toString self := self.grid.map (·|>.map toString |>.foldl String.append ""|>.append "\n")
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

def pcircuit := (return Circuit.ofChar) <*> cell

def parser := (return Data.new) <*>many (many pcircuit <* eol)

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
