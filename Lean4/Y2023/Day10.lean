import Mathlib.Tactic
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
-- import «AoC».Mat1
import «AoC».Rect
import «AoC».Parser

namespace Y2023.Day10
open CiCL CoP TwoDimensionalVector

-- def Pos : Type := Nat × Nat
-- deriving BEq, Hashable, Repr
-- def Pos.mk (y x : Nat) := (y, x)
-- instance : Inhabited Pos where default := Pos.mk 0 0
-- instance : ToString Pos where toString s := s!"P({s.1}, {s.2})"
-- instance : LT Pos where lt (a b : Pos) := a.1 < b.1 ∧ a.2 < b.2

-- def Pos.double (a : Pos) : Pos := (2 * a.1, 2 * a.2)
-- example (y x : Nat) : Pos.mk (2 * y) (2 * x) = Pos.double (Pos.mk y x) := by simp [Pos.mk, Pos.double]

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

-- #eval makeNeighbors (Pos.mk 10 10) (Pos.mk 0 0)
-- #eval makeNeighbors (Pos.mk 10 10) (Pos.mk 9 7)
-- #eval makeNeighbors (Pos.mk 10 10) (Pos.mk 10 10)

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
  -- let (dy, dx)   := both2 (fun x y ↦ Int.ofNat x - Int.ofNat y) now pre
  -- let trans      := fun x y ↦ Int.ofNat x + y |>.toNat
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
open Std

def Pos : Type := Nat × Nat
deriving BEq, Hashable, Repr
def Pos.mk (y x : Nat) := (y, x)
instance : Inhabited Pos where default := Pos.mk 0 0
instance : ToString Pos where toString s := s!"P({s.1}, {s.2})"
instance : LT Pos where lt (a b : Pos) := a.1 < b.1 ∧ a.2 < b.2

inductive PropagateState where
  | Wall       : PropagateState
  | Propagated : PropagateState
  | ToExpand   : PropagateState
  | Unknown    : PropagateState
deriving BEq, Repr

instance : Inhabited PropagateState where default := .Unknown

@[inline] def index (size : Pos) (p : Pos) : Nat := p.fst * size.snd + p.snd
@[inline] def index' (size : Pos) (n: Nat) : Pos := (n / size.snd, n % size.snd)
-- #eval index' (10, 10) 10
-- #eval index' (10, 10) 15

theorem index_index'_is_id (size : Pos) (h : 0 < size.2) : ∀ p : Pos, p < size → index' size (index size p) = p := by
  intro p Q
  dsimp [index, index']
  have X : (p.1 * size.2 + p.2) / size.2 = p.1 := by
    have D1 : size.2 ∣ (p.1 * size.2) := by exact Nat.dvd_mul_left size.2 p.1
    have D2 : (p.1 * size.2) / size.2 = p.1 := by exact Nat.mul_div_left p.1 h
    calc (p.1 * size.2 + p.2) / size.2
      = p.1 * size.2 / size.2 + p.2 / size.2 := by rw [Nat.add_div_of_dvd_right D1]
      _ = p.1 + p.2 / size.2 := by rw [D2]
      _ = p.1 + 0 := by rw [Nat.div_eq_of_lt Q.right]
      _ = p.1 := by simp
  have Y : (p.1 * size.2 + p.2) % size.2 = p.2 := by
    have D1 : (p.1 * size.2) % size.2 = 0 := by exact Nat.mul_mod_left p.1 size.2
    have D2 : p.2 % size.2 < size.2 := by exact Nat.mod_lt p.2 h
    have D3 : p.1 * size.2 % size.2 + p.2 % size.2 < size.2 := by
      calc p.1 * size.2 % size.2 + p.2 % size.2 = 0 + p.2 % size.2 := by rw [D1]
      _ = p.2 % size.2 := by simp
      _ < size.2 := by exact D2
    calc (p.1 * size.2 + p.2) % size.2
      = (p.1 * size.2) % size.2 + p.2 % size.2 := by exact Nat.add_mod_of_add_mod_lt D3
      _ = p.2 % size.2 := by simp [D1]
      _ = p.2 := by exact Nat.mod_eq_of_lt Q.right
  rw [X, Y]
  rfl

def map_of (size : Dim2) (locs : List Dim2) : Array PropagateState :=
  locs.foldl
    (fun map pos ↦ map.set! (size.index pos) PropagateState.Wall)
    (Array.mkArray (size.y.toNat * size.x.toNat) PropagateState.Unknown)

def makeNeighborsₚ (size s : Pos) : List Pos :=
  [(Ordering.lt, Ordering.eq), (.gt, .eq), (.eq, .lt), (.eq, .gt)]
    |>.filterMap
      (fun d => if
        !( (s.1    == 0       && d.fst == .lt)
        || (size.1 ≤ s.1 + 1  && d.fst == .gt)
        ||  size.1 < s.1 + 1
        || (s.2    == 0       && d.snd == .lt)
        || (size.2 = s.2 + 1  && d.snd == .gt)
        ||  size.2 < s.2 + 1)
        then some (Pos.mk
          (match d.fst with | .lt => s.1 - 1 | .eq => s.1 | .gt => s.1 + 1)
          (match d.snd with | .lt => s.2 - 1 | .eq => s.2 | .gt => s.2 + 1))
        else none)

def expand (self : Array PropagateState) (size : Dim2) (n : Nat) : Array PropagateState :=
  makeNeighbors size (size.index' n)
    |>.foldl
      (fun m q ↦ match m.get! (size.index q) with
        | .Unknown => m.set! (size.index q) .ToExpand
        | _ => m)
      (self.set! n .Propagated)

/-
- Switch to 1D scan from 28 scan
-/
-- #eval List.iota 4 |>.mapIdx fun i x ↦ (i, x)

partial def loop (m : Array PropagateState) (size : Dim2) : Array PropagateState :=
  let r := m.foldl
    (fun (i, m, u) p ↦ (
      i + 1, if p == PropagateState.ToExpand then (expand m size i, true) else (m, u)))
    (0, m, false)
  if r.snd.snd then loop r.snd.fst size else r.snd.fst

def propagate (self : Array PropagateState) (size : Dim2) : Array PropagateState := loop s size
  where
    s := self.set! (size.index (0, 0)) .ToExpand

/-!
  1. pick the looping route
  2. double the scale
  3. draw the loop
  4. run propagation
  5. count the unmarked cells
-/

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

def Pos.interpolate (p : Dim2) (q : Dim2) : Dim2 :=
  let (p', q') := both Dim2.double (p, q)
  ((p'.y + q'.y) / 2, (p'.x + q'.x) / 2)

-- #eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Dim2 → List Dim2
  | []          => []
  | p :: []     => [p.double]
  | p :: q :: l => [p.double, Pos.interpolate p q] ++ scaleUp (q :: l)

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
