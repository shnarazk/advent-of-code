import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Day10
open Std CiCL CoP

def Pos : Type := Nat × Nat
deriving BEq, Repr, ToString

def Pos.lt (a : Pos) (b : Pos) : Bool := join and <| both2 (fun i j => i < j) a b

def Pos.double : Pos → Pos := both (· * 2)

-- #eval Pos.double ((3, 4) : Pos)
-- #eval Pos.double ((3, 5) : Pos)

def makeNeighbors (size s : Pos) : List Pos :=
  [(s.fst + 1, s.snd + 0), (s.fst - 1, s.snd + 0), (s.fst + 0, s.snd + 1), (s.fst + 0, s.snd - 1)]
    |>.filter (Pos.lt · size)

-- #eval makeNeighbors (10, 10) (0, 0)

def makeVecs (size start : Pos) : List (Pos × Pos) := makeNeighbors size start |>.map ((start, ·))

-- #eval makeVecs (10, 10) (2, 2)

instance : ToString Pos where
  toString s := s!"P({s.fst}, {s.snd})"

inductive Circuit where
  | v : Circuit
  | h : Circuit
  | l : Circuit
  | j : Circuit
  | k : Circuit
  | f : Circuit
  | s : Circuit
  | x : Circuit
deriving BEq, Repr

instance : Inhabited Circuit where
  default := Circuit.x

instance : ToString Circuit where
  toString s :=
  match s with
  | .v => "|"
  | .h => "-"
  | .l => "L"
  | .j => "J"
  | .k => "7"
  | .f => "F"
  | .s => "S"
  | _  => " "

def Circuit.ofChar (c : Char) : Circuit :=
  match c with
  | '|' => .v
  | '-' => .h
  | 'L' => .l
  | 'J' => .j
  | '7' => .k
  | 'F' => .f
  | 'S' => .s
  |  _  => .x

-- #eval (Circuit.ofChar 'f') |> toString

def startPosition (self : Mat1 Circuit) : Pos :=
  self.findIdx? (· == Circuit.s) |>.getD (0, 0)

def dest (mat : Mat1 Circuit) (vec : Pos × Pos) : Pos × Pos :=
  let (pre, pos) := vec
  let (dy, dx)   := both2 (fun x y => Int.ofNat x - Int.ofNat y) pos pre
  let trans      := fun x y => Int.ofNat x + y |>.toNat
  match uncurry mat.get? pos with
  | some .v           => (pos, both2 trans pos ( dy,   0))
  | some .h           => (pos, both2 trans pos (  0,  dx))
  | some .l | some .k => (pos, both2 trans pos ( dx,  dy))
  | some .j | some .f => (pos, both2 trans pos (-dx, -dy))
  | _                 => (pos, pos)

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

def parser := (return Mat1.of2DMatrix) <*>many (many pcircuit <* eol)

end parser

namespace part1

def loop_len (self : Mat1 Circuit) (limit : Nat) (start : Pos) (len : Nat) (vec : Pos × Pos) : Nat :=
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
    |>.maximum? |>.getD 0 |> (· / 2)

end part1

structure Map where
  new ::
  size : Pos
  cells : Array Bool

namespace Map

-- #eval #[1, 2].isEmpty
-- #check @Fin.ofNat' 10 3

def countElements (size: Pos) : Nat := size.fst * size.snd

@[inline]
def index (self : Map) (p : Pos) : Nat := p.fst * self.size.snd + p.snd

@[inline]
def contains (self : Map) (p : Pos) : Bool := self.cells.get! $ Map.index self p

@[inline]
def set (self : Map) (p : Pos) : Map :=
  { self with cells := self.cells.set! (Map.index self p) true }

def of (size : Pos) (locs : List Pos) : Map :=
  locs.foldl
    (fun map pos => Map.set map pos)
    (Map.new size (Array.mkArray (countElements size) false))

end Map

namespace part2
open Lean Data

/-!
  1. pick the looping route
  2. double the scale
  3. draw the loop
  4. run propagation
  5. count the unmarked cells
-/

def mkLoop (self : Mat1 Circuit) (limit : Nat) (start : Pos) (path : List Pos) (vec : Pos × Pos)
    : List Pos :=
  match limit with
  | 0        => []
  | lim' + 1 =>
    let v' := dest self vec
    if v'.fst == v'.snd
    then if v'.snd == start then path ++ [v'.fst] else []
    else mkLoop self lim' start (path ++ [v'.fst]) v'

def Pos.interpolate (p : Pos) (q : Pos) : Pos :=
  let p' := Pos.double p
  let q' := Pos.double q
  ((p'.fst + q'.fst) / 2, (p'.snd + q'.snd) / 2)

-- #eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Pos → List Pos
  | []          => []
  | p :: []     => [Pos.double p]
  | p :: q :: l => [Pos.double p, Pos.interpolate p q] ++ scaleUp (q :: l)

-- #eval makeNeighbors (10, 10) (0, 0)

def propagate (limit : Nat) (linked : Map) (toVisit : List Pos) : Map :=
  match limit with
  | 0       => linked
  | lim + 1 =>
  match toVisit with
  | [] => linked
  | _ =>
    toVisit.map (makeNeighbors linked.size)
      |>.join
      |>.foldl
        (fun lt e => if lt.fst.contains e then lt else (lt.fst.set e, e :: lt.snd))
        (linked, [])
      |> uncurry (propagate lim)

def isEven : Pos → Bool := (join and) ∘ (both (· % 2 == 0))

def solve (m: Mat1 Circuit) : Nat :=
  let st := startPosition m
  let sp := m.shape
  let loop := makeVecs sp st
    |>.map (mkLoop m m.size st [st] .)
    |>.foldl (fun best cand => if best.length < cand.length then cand else best) []
    |> scaleUp
  let map := propagate m.size (Map.of (Pos.double sp) loop) [(0, 0)]
  List.range sp.fst
    |>.foldl (fun count y =>
      List.range sp.snd
        |>.filter (fun x => !map.contains (Pos.double (y, x)))
        |>.length
        |> (· + count))
      0

-- #eval List.range 9

end part2

end Day10

def day10 (ext : Option String) : IO Answers := do
  if let some (some m) := AoCParser.parse Day10.parser.parser (← dataOf 2023 10 ext)
  then return (s!"{Day10.part1.solve m}", s!"{Day10.part2.solve m}")
  else return ("parse error", "")
