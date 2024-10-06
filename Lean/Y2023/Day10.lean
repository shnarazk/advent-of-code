import Batteries
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2023.Day10
open CiCL CoP

def Pos : Type := Nat × Nat
deriving BEq, Hashable, Repr, ToString

instance : Inhabited Pos where default := (0, 0)
instance : ToString Pos where toString s := s!"P({s.fst}, {s.snd})"

def Pos.lt (a : Pos) (b : Pos) : Bool := join and <| both2 (fun i j ↦ i < j) a b

def Pos.double : Pos → Pos := both (· * 2)

-- #eval Pos.double ((3, 4) : Pos)
-- #eval Pos.double ((3, 5) : Pos)

def makeNeighbors (size s : Pos) : List Pos :=
  [(s.fst + 1, s.snd + 0), (s.fst - 1, s.snd + 0), (s.fst + 0, s.snd + 1), (s.fst + 0, s.snd - 1)]
    |>.filter (Pos.lt · size)

-- #eval makeNeighbors (10, 10) (0, 0)

def makeVecs (size start : Pos) : List (Pos × Pos) :=
  makeNeighbors size start
    |>.map ((start, ·))

-- #eval makeVecs (10, 10) (2, 2)

inductive Circuit where
  | v : Circuit
  | h : Circuit
  | l : Circuit
  | j : Circuit
  | s : Circuit
  | x : Circuit
deriving BEq, Repr

instance : Inhabited Circuit where
  default := Circuit.x

instance : ToString Circuit where
  toString c :=
  match c with
  | .v => "|"
  | .h => "-"
  | .l => "L"
  | .j => "J"
  | .s => "S"
  | _  => " "

def Circuit.ofChar (c : Char) : Circuit :=
  match c with
  | '|' => .v
  | '-' => .h
  | 'L' => .l
  | 'J' => .j
  | '7' => .l -- .k
  | 'F' => .j -- .f
  | 'S' => .s
  |  _  => .x

-- #eval (Circuit.ofChar 'f') |> toString

def startPosition (self : Mat1 Circuit) : Pos :=
  self.findIdx? (· == Circuit.s) |>.getD (0, 0)

def dest (mat : Mat1 Circuit) (vec : Pos × Pos) : Pos × Pos :=
  let (pre, now) := vec
  let (dy, dx)   := both2 (fun x y ↦ Int.ofNat x - Int.ofNat y) now pre
  let trans      := fun x y ↦ Int.ofNat x + y |>.toNat
  let diff := match uncurry mat.get? now with
  | some .v => ( dy,   0)
  | some .h => (  0,  dx)
  | some .l => ( dx,  dy)
  | some .j => (-dx, -dy)
  |       _ => (  0,   0)
  (now, both2 trans now diff)

namespace parser
open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := pchar '|'
  <|> pchar '-'
  <|> pchar 'L'
  <|> pchar 'J'
  <|> pchar '7'
  <|> pchar 'F'
  <|> pchar '.'
  <|> pchar 'S'

def parse := AoCParser.parse parser
  where
    pcircuit := (return Circuit.ofChar) <*> cell
    parser := (return Mat1.of2DMatrix) <*> many (many pcircuit <* eol)

end parser

namespace part1

def loop_len
    (self : Mat1 Circuit)
    (limit : Nat)
    (start : Pos)
    (len : Nat)
    (vec : Pos × Pos)
    : Nat :=
  match limit with
  | 0        => 0
  | lim' + 1 =>
    let v' := dest self vec
    if v'.fst == v'.snd
    then if v'.snd == start then len + 1 else 0
    else loop_len self lim' start (len + 1) v'

def solve (m : Mat1 Circuit) : Nat :=
  makeVecs m.shape (startPosition m)
    |>.map (loop_len m m.size (startPosition m) 0 .)
    |>.max? |>.getD 0 |> (· / 2)

end part1

namespace part2
open Std

inductive PropagateState where
  | Wall       : PropagateState
  | Propagated : PropagateState
  | ToExpand   : PropagateState
  | Unknown    : PropagateState
deriving BEq, Repr

instance : Inhabited PropagateState where default := .Unknown

@[inline]
def index (size : Pos) (p : Pos) : Nat := p.fst * size.snd + p.snd

def map_of (size : Pos) (locs : List Pos) : Array PropagateState :=
  locs.foldl
    (fun map pos ↦ map.set! (index size pos) PropagateState.Wall)
    (Array.mkArray (size.fst * size.snd) PropagateState.Unknown)

def expand (self : Array PropagateState) (size : Pos) (p : Pos) : Array PropagateState :=
  makeNeighbors size p
    |>.foldl
      (fun m q ↦ match m.get! (index size q) with
        | PropagateState.Unknown => m.set! (index size q) PropagateState.ToExpand
        | _ => m
      )
      (self.set! (index size p) PropagateState.Propagated)

partial def loop (m : Array PropagateState) (size : Pos) : Array PropagateState :=
  let r := List.range size.fst
    |>.foldl
      (fun mm y ↦
        (List.range size.snd).foldl
          (fun mm x ↦
            if m.get! (index size (y, x)) == .ToExpand
            then (expand mm.fst size (y, x), true)
            else mm)
          mm
      )
      (m, false)
  if r.snd then loop r.fst size else r.fst

def propagate (self : Array PropagateState) (size : Pos) : Array PropagateState := loop s size
  where
    s := self.set! (index size (0, 0)) .ToExpand

/-!
  1. pick the looping route
  2. double the scale
  3. draw the loop
  4. run propagation
  5. count the unmarked cells
-/

def mkLoop
    (self : Mat1 Circuit)
    (limit : Nat)
    (start : Pos)
    (path : List Pos)
    (vec : Pos × Pos)
    : List Pos :=
  match limit with
  | 0        => []
  | lim' + 1 =>
    let v' := dest self vec
    if v'.fst == v'.snd
    then if v'.snd == start then path ++ [v'.fst] else []
    else mkLoop self lim' start (path ++ [v'.fst]) v'

def Pos.interpolate (p : Pos) (q : Pos) : Pos :=
  let (p', q') := both Pos.double (p, q)
  ((p'.fst + q'.fst) / 2, (p'.snd + q'.snd) / 2)

-- #eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Pos → List Pos
  | []          => []
  | p :: []     => [Pos.double p]
  | p :: q :: l => [Pos.double p, Pos.interpolate p q] ++ scaleUp (q :: l)

def solve (m: Mat1 Circuit) : Nat :=
  let st := startPosition m
  let sp := m.shape
  let loop := makeVecs sp st
    |>.map (mkLoop m m.size st [st] .)
    |>.foldl (fun best cand ↦ if best.length < cand.length then cand else best) []
    |> scaleUp
    let size := Pos.double sp
  let a_map := propagate (map_of size loop) size
  List.range sp.fst
    |>.foldl (fun sum y ↦
      List.range sp.snd
        |>.filter (fun x ↦ PropagateState.Unknown == a_map.get! (index size (Pos.double (y, x))))
        |>.length
        |> (· + sum))
      0

end part2

protected def solve (ext : Option String) : IO Answers := do
  if let some (some m) := parser.parse (← dataOf 2023 10 ext)
  then return (s!"{part1.solve m}", s!"{part2.solve m}")
  else return ("parse error", "")

end Y2023.Day10
