import Mathlib.Tactic
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Rect
import «AoC».Parser

namespace Y2023.Day10
open CiCL CoP TwoDimensionalVector

def makeNeighbors (size s : Dim2) : List Dim2 :=
  [(Ordering.lt, Ordering.eq), (.gt, .eq), (.eq, .lt), (.eq, .gt)]
    |>.filterMap
      (fun d => if
        !( (s.y    == 0       && d.fst == .lt)
        || (size.y ≤ s.y + 1  && d.fst == .gt)
        ||  size.y < s.y + 1
        || (s.x    == 0       && d.snd == .lt)
        || (size.x = s.x + 1  && d.snd == .gt)
        ||  size.x < s.x + 1)
        then some (Dim2.mk
          (match d.fst with | .lt => s.y - 1 | .eq => s.y | .gt => s.y + 1)
          (match d.snd with | .lt => s.x - 1 | .eq => s.x | .gt => s.x + 1))
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
  self.findPosition? (· == Circuit.s) |>.unwrapOr (Dim2.mk 0 0)

def dest (mat : Rect Circuit) (vec : Dim2 × Dim2) : Dim2 × Dim2 :=
  let (pre, now) := vec
  let diff := now - pre
  let dy := diff.y
  let dx := diff.x
  let diff := match mat.get? now with
  | some .v => Dim2.mk dy   0
  | some .h => Dim2.mk  0  dx
  | some .l => Dim2.mk dx  dy
  | some .j => Dim2.mk (-dx) (-dy)
  |       _ => Dim2.mk  0   0
  (now, now + diff)

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
    if v'.fst == v'.snd
      then if v'.snd == start then len + 1 else 0
      else loop_len self lim' start (len + 1) v'

def solve (m : Rect Circuit) : Nat :=
  makeVecs m.shape (startPosition m)
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
    (fun map pos ↦ map.set! (size.index pos) PropagateState.Wall)
    (Array.mkArray (size.y.toNat * size.x.toNat) PropagateState.Unknown)

def expand (self : Array PropagateState) (size : Dim2) (n : Nat) : Array PropagateState :=
  makeNeighbors size (size.index' n)
    |>.foldl
      (fun m q ↦ match m.get! (size.index q) with
        | .Unknown => m.set! (size.index q) .ToExpand
        | _ => m)
      (self.set! n .Propagated)

/-
- Switch to 1D scan from 28 scan
-- #eval List.iota 4 |>.mapIdx fun i x ↦ (i, x)
-/
partial def loop (m : Array PropagateState) (size : Dim2) : Array PropagateState :=
  let r := m.foldl
    (fun (i, m, u) p ↦ (
      i + 1, if p == PropagateState.ToExpand then (expand m size i, true) else (m, u)))
    (0, m, false)
  if r.snd.snd then loop r.snd.fst size else r.snd.fst

def propagate (self : Array PropagateState) (size : Dim2) : Array PropagateState := loop s size
  where
    s := self.set! (size.index (0, 0)) .ToExpand

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
    if v'.fst == v'.snd
      then if v'.snd == start then path ++ [v'.fst] else []
      else mkLoop self lim' start (path ++ [v'.fst]) v'

def interpolate (p : Dim2) (q : Dim2) : Dim2 :=
  let (p', q') := both Dim2.double (p, q)
  ((p'.y + q'.y) / 2, (p'.x + q'.x) / 2)

-- #eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Dim2 → List Dim2
  | []          => []
  | p :: []     => [p.double]
  | p :: q :: l => [p.double, interpolate p q] ++ scaleUp (q :: l)

/-!
  1. pick the looping route
  2. double the scale
  3. draw the loop
  4. run propagation
  5. count the unmarked cells
-/
def solve (m: Rect Circuit) : Nat :=
  let st := startPosition m
  let shape := m.shape
  let loop := makeVecs shape st
    |>.map (mkLoop m m.area st [st] ·)
    |>.foldl (fun best cand ↦ if best.length < cand.length then cand else best) []
    |> scaleUp
  let size := Dim2.double shape
  let a_map := propagate (map_of size loop) size
  List.range shape.y.toNat
    |>.foldl (fun sum y ↦
      List.range shape.x.toNat
        |>.filter (fun x ↦ PropagateState.Unknown == a_map.get! (size.index (Dim2.mk y x).double))
        |>.length
        |> (· + sum))
      0

end part2

def solve := AocProblem.config 2023 10 (parser.parse · |>.join) part1.solve part2.solve

end Y2023.Day10
