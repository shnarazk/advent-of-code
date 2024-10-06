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
  let (dy, dx)   := both2 (fun x y => Int.ofNat x - Int.ofNat y) now pre
  let trans      := fun x y => Int.ofNat x + y |>.toNat
  let diff := match uncurry mat.get? now with
  | some .v => ( dy,   0)
  | some .h => (  0,  dx)
  | some .l => ( dx,  dy) -- | some .k => ( dx,  dy)
  | some .j => (-dx, -dy) -- | some .f => (-dx, -dy)
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

def pcircuit := (return Circuit.ofChar) <*> cell

def parser := (return Mat1.of2DMatrix) <*> many (many pcircuit <* eol)

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
  size : Pos
  cells : Array (Option Bool)
deriving BEq

instance : Inhabited Map where
  default := Map.mk (0, 0) #[]

namespace Map

-- #eval #[1, 2].isEmpty
-- #check @Fin.ofNat' 10 3

def countElements (size: Pos) : Nat := size.fst * size.snd

@[inline]
def index (self : Map) (p : Pos) : Nat := p.fst * self.size.snd + p.snd

@[inline]
def checked (self : Map) (p : Pos) : Bool := self.cells.get! (Map.index self p) != none

@[inline]
def set (self : Map) (p : Pos) (b : Bool) : Map :=
  { self with cells := self.cells.set! (self.index p) (some b) }

def of (size : Pos) (locs : List Pos) : Map :=
  locs.foldl
    (fun map pos => Map.set map pos false)
    (Map.mk size (Array.mkArray (countElements size) none))

end Map

namespace part2
open Std

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

partial def propagate0 (args : Map × HashSet Pos) : Map :=
  if args.2.isEmpty
  then args.1
  else
    (args.2.fold
      (fun lh p ↦ (makeNeighbors args.1.size p).foldl
        (fun lh q ↦ if lh.fst.checked q then lh else (lh.fst.set q false, lh.snd.insert q))
        lh)
      (args.1, HashSet.empty 100000))
    |> propagate0

partial def propagate (linked : Map) (toVisit : HashSet Pos) : Map :=
  if toVisit.isEmpty
  then linked
  else
    toVisit.fold
      (fun lh p ↦ (makeNeighbors linked.size p).foldl
        (fun lh q ↦ if lh.fst.checked q then lh else (lh.fst.set q false, lh.snd.insert q))
        lh)
      (linked, (HashSet.empty 100000 : HashSet Pos))
    |> uncurry propagate

partial def propagate_old : Map × List Pos → Map
  | (linked, []) => linked
  | (linked, toVisit) =>
    toVisit.map (makeNeighbors linked.size)
      |>.join
      |>.foldl
        (fun lt e => if lt.fst.checked e then lt else (lt.fst.set e false, e :: lt.snd))
        (linked, [])
      |> propagate_old

def solve (m: Mat1 Circuit) : Nat :=
  let st := startPosition m
  let sp := m.shape
  let loop := makeVecs sp st
    |>.map (mkLoop m m.size st [st] .)
    |>.foldl (fun best cand => if best.length < cand.length then cand else best) []
    |> scaleUp
  -- let a_map := propagate0 (Map.of (Pos.double sp) loop, HashSet.empty.insert (0, 0))
  -- let a_map := propagate (Map.of (Pos.double sp) loop) (HashSet.empty.insert (0, 0))
  let a_map := propagate_old (Map.of (Pos.double sp) loop,  [(0, 0)])
  List.range sp.fst
    |>.foldl (fun count y =>
      List.range sp.snd
        |>.filter (fun x => !a_map.checked (Pos.double (y, x)))
        |>.length
        |> (· + count))
      0

-- #eval List.range 9

end part2

protected def solve (ext : Option String) : IO Answers := do
  if let some (some m) := AoCParser.parse parser.parser (← dataOf 2023 10 ext)
  then return (s!"{part1.solve m}", s!"{part2.solve m}")
  else return ("parse error", "")

end Y2023.Day10
