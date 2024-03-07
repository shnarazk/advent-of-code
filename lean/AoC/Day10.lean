import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day10
open Std

def Pos : Type := Nat × Nat
deriving BEq, Repr, ToString, Hashable

def makeNeighbors (s : Pos) : List Pos :=
  [(s.fst + 1, s.snd + 0), (s.fst - 1, s.snd + 0), (s.fst + 0, s.snd + 1), (s.fst + 0, s.snd - 1)]

#eval makeNeighbors (0, 0)

def makeVecs (start : Pos) : List (Pos × Pos) := makeNeighbors start |>.map ((start, ·))

#eval makeVecs (2, 2)

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

def seek (a: Array (Array Circuit)) (n : Nat) (target : Circuit) : Pos :=
  if h : n < a.size then
    let l := a[n]'h
    match Array.findIdx? l (· == target) with
    | some m => (n, m)
    | _      => seek a (n + 1) target
  else (0, 0)
termination_by a.size - n

def Data.start (self : Data) : Pos := seek self.grid 0 Circuit.S

def Data.at (self : Data) (pos : Pos) : Option Circuit :=
  (self.grid[pos.fst]?) >>= (·[pos.snd]?)

def Data.dest (c : Data) (vec : Pos × Pos) : Pos × Pos :=
  let (pre, pos) := vec
  let dy : Int := Int.ofNat pos.fst - Int.ofNat pre.fst
  let dx : Int := Int.ofNat pos.snd - Int.ofNat pre.snd
  match c.at pos with
  | some .v /- | -/ => (pos, (Int.toNat $ Int.ofNat pos.fst + dy , Int.toNat $ Int.ofNat pos.snd     ))
  | some .h /- - -/ => (pos, (Int.toNat $ Int.ofNat pos.fst      , Int.toNat $ Int.ofNat pos.snd + dx))
  | some .l /- L -/ => (pos, (Int.toNat $ Int.ofNat pos.fst + dx , Int.toNat $ Int.ofNat pos.snd + dy))
  | some .j /- J -/ => (pos, (Int.toNat $ Int.ofNat pos.fst - dx , Int.toNat $ Int.ofNat pos.snd - dy))
  | some .k /- 7 -/ => (pos, (Int.toNat $ Int.ofNat pos.fst + dx , Int.toNat $ Int.ofNat pos.snd + dy))
  | some .f /- F -/ => (pos, (Int.toNat $ Int.ofNat pos.fst - dx , Int.toNat $ Int.ofNat pos.snd - dy))
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

partial def loop_len (self : Data) (start : Pos) (len : Nat) (vec : Pos × Pos) : Nat :=
  let v' := self.dest vec
  if v'.fst == v'.snd
  then if v'.snd == start then len + 1 else 0
  else loop_len self start (len + 1) v'

def solve (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some m =>
    let len := (makeVecs m.start) |>.map (loop_len m m.start 0 .)
        |>.maximum? |>.getD 0 |> (· / 2)
    IO.println s!"  part1: {len}"
  return ()

end part1

namespace part2
open Lean

/-!
  1. [x] pick the looping route
  2. [x] double the scale
  3. [x] draw the loop
  4. [ ] run propagation
  5. [ ] count the unmarked cells
-/

partial def loop (self : Data) (start : Pos) (path : List Pos) (vec : Pos × Pos)
    : List Pos :=
  let v' := self.dest vec
  if v'.fst == v'.snd
  then if v'.snd == start then start :: path else []
  else loop self start (path ++ [v'.snd]) v'

def Pos.double (p : Pos) : Pos := (p.fst * 2, p.snd * 2)

#eval Pos.double ((3, 4) : Pos)
#eval Pos.double ((3, 5) : Pos)

def Pos.interpolate (p : Pos) (q : Pos) : Pos :=
  let p' := Pos.double p
  let q' := Pos.double q
  ((p'.fst + q'.fst) / 2, (p'.snd + q'.snd) / 2)

#eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Pos → List Pos
  | [] => []
  | pos :: [] => [Pos.double pos]
  | p :: q :: l' => [Pos.double p, Pos.interpolate p q, Pos.double p] ++ scaleUp (q :: l')

def toHashMap (elements : List Pos) : HashSet Pos :=
  elements.foldl (fun h e => h.insert e) HashSet.empty

#eval makeNeighbors (0, 0)

def Pos.lt (self : Pos) (other : Pos) : Bool := self.fst < other.fst && self.snd < other.snd

partial def propagate (size : Pos) (linked : HashSet Pos) (toVisit : List Pos) : HashSet Pos :=
  match toVisit with
  | [] => linked
  | _ =>
    let x := toVisit.map makeNeighbors |>.join |>.filter (Pos.lt · size)
    let (l', t') := x.foldl (fun (l, t) e =>
        if l.contains e then (l, t) else (l.insert e, t ++ [e]))
      (linked, [])
    propagate size l' t'

def solve (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part2: parse error"
  | some m =>
    let size := (m.grid.size * 2, m.grid[0]!.size * 2)
    let loop := (makeVecs m.start) |>.map (loop m m.start [] .)
        |>.foldl (fun best cand => if best.length < cand.length then cand else best) []
        |> scaleUp
    let map := propagate size (toHashMap loop) [(0, 0)]
    IO.println s!"  part2: {loop.length}, {size} {map.size}"
    let ans := (size.fst * size.snd - map.size) / 4
    IO.println s!"  part2: {ans}"
  return ()

end part2

end Day10

def day10 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 10 ext
  Day10.part1.solve data
  Day10.part2.solve data
