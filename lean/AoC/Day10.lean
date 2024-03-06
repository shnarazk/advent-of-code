import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day10
open Std

def Pos : Type := Nat × Nat
deriving BEq, Repr, ToString

instance : ToString Pos where
  toString s := s!"P({s.fst}, {s.snd})"

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

partial def seek (a: Array (Array Circuit)) (n : Nat) (target : Circuit) : Option Pos :=
  match a.get? n with
  | none => some (0, 0)
  | some l =>
    match Array.findIdx? l (· == target) with
    | some m => some (n, m)
    | _ => seek a (n + 1) target

def Data.start (self : Data) : Pos :=
  match seek self.grid 0 Circuit.S with
  | some p => p
  | none =>(0, 0)

def Data.at (self : Data) (pos : Pos) : Option Circuit :=
  (self.grid[pos.fst]?) >>= (·[pos.snd]?)

partial def Data.dest (c : Data) (vec : Pos × Pos) : Pos × Pos :=
  let (pre, pos) := vec
  let dy := pos.fst - pre.fst
  let dx := pos.snd - pre.snd
  match c.at pos with
  | some .v /- | -/ => (pos, (pos.fst + dy , pos.snd     ))
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

partial def Data.loop_len (self : Data) (vec : Pos × Pos) : Nat :=
  let v' := self.dest vec
  if v'.fst == v'.snd
  then 0
  else 1 + self.loop_len v'

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

def makeNeighbors (s : Pos) : List Pos :=
  [(s.fst + 1, s.snd + 0), (s.fst - 1, s.snd + 0), (s.fst + 0, s.snd + 1), (s.fst + 0, s.snd - 1)]

#eval makeNeighbors (0, 0)

def makeVecs (start : Pos) : List (Pos × Pos) := makeNeighbors start |>.map ((·, start))

#eval makeVecs (2, 2)

namespace part1
def solve (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some map =>
    let _ ← (makeVecs map.start) |>.mapM (fun x => IO.println s!"{x}")
    IO.println s!"{(makeVecs map.start) |>.map map.loop_len}"
  return ()

end part1

namespace part2

def solve (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part2: parse error"
  | some d => IO.println s!"  part2: {d.start}"
  return ()

end part2

end Day10

def day10 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 10 ext
  Day10.part1.solve data
  Day10.part2.solve data
