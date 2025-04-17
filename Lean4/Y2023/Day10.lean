import «AoC».Basic
import «AoC».Combinator
import «AoC».Rect64
import «AoC».Parser

namespace Y2023.Day10

open CiCL CoP TwoDimensionalVector64

abbrev Dim2 := UInt64 × UInt64

def makeNeighbors (size s : Dim2) : List Dim2 :=
  [(Ordering.lt, Ordering.eq), (.gt, .eq), (.eq, .lt), (.eq, .gt)]
    |>.filterMap
      (fun d => if
        !( (s.fst    == 0         && d.fst == .lt)
        || (size.fst ≤ s.fst + 1  && d.fst == .gt)
        ||  size.fst < s.fst + 1
        || (s.snd    == 0         && d.snd == .lt)
        || (size.snd = s.snd + 1  && d.snd == .gt)
        ||  size.snd < s.snd + 1)
        then some (
          (match d.fst with | .lt => s.fst - 1 | .eq => s.fst | .gt => s.fst + 1),
          (match d.snd with | .lt => s.snd - 1 | .eq => s.snd | .gt => s.snd + 1))
        else none)

def makeVecs (size start : Dim2) : List (Dim2 × Dim2) :=
  (makeNeighbors size start).map ((start, ·))

-- #eval makeVecs (10, 10) (2, 2)

inductive Circuit where
  | v : Circuit
  | h : Circuit
  | l : Circuit
  | j : Circuit
  | s : Circuit
  | x : Circuit
deriving BEq, Repr

instance : Inhabited Circuit where default := Circuit.x

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

def startPosition (self : Rect Circuit) : Dim2 :=
  self.findPosition? (· == Circuit.s) |>.unwrapOr (0, 0)

def dest (mat : Rect Circuit) (vec : Dim2 × Dim2) : Dim2 × Dim2 :=
  let (pre, now) := vec
  let dy := now.fst - pre.fst
  let dx := now.snd - pre.snd
  let diff := match mat.get? now with
    | some .v => (now.fst + dy, now.snd)
    | some .h => (now.fst     , now.snd + dx)
    | some .l => (now.fst + dx, now.snd + dy)
    | some .j => (now.fst - dx, now.snd - dy)
    |       _ => now
  (now, diff)

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
    parser := (return Rect.of2DMatrix) <*> many (many pcircuit <* eol)

end parser

namespace part1

def loop_len
    (self : Rect Circuit)
    (limit : Nat)
    (start : Dim2)
    (len : Nat)
    (vec : Dim2 × Dim2)
    : Nat :=
  match limit with
  | 0        => 0
  | lim' + 1 =>
    let v' := dest self vec
    if v'.fst.fst == v'.snd.fst && v'.fst.snd == v'.snd.snd
      then if v'.snd.fst == start.fst && v'.snd.snd == start.snd then len + 1 else 0
      else loop_len self lim' start (len + 1) v'

def solve (m : Rect Circuit) : Nat :=
  makeVecs (m.vector.size.toUInt64 / m.width, m.width) (startPosition m)
    |>.map (loop_len m m.area (startPosition m) 0 .)
    |>.max? |>.getD 0 |> (· / 2)

end part1

namespace part2

inductive PropagateState where
  | Wall       : PropagateState
  | Propagated : PropagateState
  | ToExpand   : PropagateState
  | Unknown    : PropagateState
deriving BEq, Repr

instance : Inhabited PropagateState where default := .Unknown

def map_of (size : Dim2) (locs : List Dim2) : Array PropagateState :=
  locs.foldl
    (fun map pos ↦ map.set! (size.snd * pos.fst + pos.snd).toNat PropagateState.Wall)
    (Array.replicate (size.fst.toNat * size.snd.toNat) PropagateState.Unknown)

def expand (self : Array PropagateState) (size : Dim2) (n : Nat) : Array PropagateState :=
  makeNeighbors size (n.toUInt64 / size.snd,  n.toUInt64 % size.snd)
    |>.foldl
      (fun m q ↦ match m[(size.snd * q.fst + q.snd).toNat]! with
        | .Unknown => m.set! (size.snd * q.fst + q.snd).toNat .ToExpand
        | _ => m)
      (self.set! n .Propagated)

/-
- Switch to 1D scan from 28 scan
-- #eval List.iota 4 |>.mapIdx fun i x ↦ (i, x)
-/
partial
def loop (m : Array PropagateState) (size : Dim2) : Array PropagateState :=
  let r := m.foldl
    (fun (i, m, u) p ↦ (
      i + 1, if p == PropagateState.ToExpand then (expand m size i, true) else (m, u)))
    (0, m, false)
  if r.snd.snd then loop r.snd.fst size else r.snd.fst

def propagate (self : Array PropagateState) (size : Dim2) : Array PropagateState :=
  loop s size
  where
    s := self.set! 0 .ToExpand

def mkLoop
    (self : Rect Circuit)
    (limit : Nat)
    (start : Dim2)
    (path : List Dim2)
    (vec : Dim2 × Dim2)
    : List Dim2 :=
  match limit with
  | 0        => []
  | lim' + 1 =>
    let v' : Dim2 × Dim2 := dest self vec
    if v'.fst.fst == v'.snd.fst && v'.fst.snd == v'.snd.snd
      then if v'.snd.fst == start.fst && v'.snd.snd == start.snd then path ++ [v'.fst] else []
      else mkLoop self lim' start (path ++ [v'.fst]) v'

def interpolate (p : Dim2) (q : Dim2) : Dim2 :=
  let (p', q') := both (fun d ↦ (d.fst * 2, d.snd * 2)) (p, q)
  ((p'.fst + q'.fst) / 2, (p'.snd + q'.snd) / 2)

-- #eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Dim2 → List Dim2
  | []          => []
  | p :: []     => [(p.fst * 2, p.snd * 2)]
  | p :: q :: l => ([(p.fst * 2, p.snd * 2), interpolate p q] : List Dim2) ++ scaleUp (q :: l)

/-!
  1. pick the looping route
  2. double the scale
  3. draw the loop
  4. run propagation
  5. count the unmarked cells
-/
def solve (m: Rect Circuit) : Nat :=
  let st := startPosition m
  let shape := (m.vector.size.toUInt64 / m.width, m.width)
  let loop := makeVecs shape st
    |>.map (mkLoop m m.area st [st] ·)
    |>.foldl (fun best cand ↦ if best.length < cand.length then cand else best) []
    |> scaleUp
  let size : Dim2 := (shape.fst * 2, shape.snd * 2)
  let a_map := propagate (map_of size loop) size
  List.range shape.fst.toNat
    |>.foldl (fun sum y ↦
      List.range shape.snd.toNat
        |>.filter (fun x ↦ PropagateState.Unknown == a_map[size.snd.toNat * y * 2 + x * 2]!)
        |>.length
        |> (· + sum))
      0

end part2

def solve := AocProblem.config 2023 10 (parser.parse · |>.join) part1.solve part2.solve

end Y2023.Day10
