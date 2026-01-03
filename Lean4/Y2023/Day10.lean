module

public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec

namespace Y2023.Day10

open CiCL CoP Dim2

def makeNeighbors (size s : Idx₂) : List Idx₂ :=
  [(Ordering.lt, Ordering.eq), (.gt, .eq), (.eq, .lt), (.eq, .gt)]
    |>.filterMap
      (fun d => if
        !( (s.fst    == 0         && d.fst == .lt)
        || (size.fst ≤ s.fst + 1  && d.fst == .gt)
        ||  size.fst < s.fst + 1
        || (s.snd    == 0         && d.snd == .lt)
        || (size.snd = s.snd + 1  && d.snd == .gt)
        ||  size.snd < s.snd + 1)
        then
          let q := (
          (match d.fst with | .lt => s.fst - 1 | .eq => s.fst | .gt => s.fst + 1),
          (match d.snd with | .lt => s.snd - 1 | .eq => s.snd | .gt => s.snd + 1))
        if p : (0, 0) ≤ q then some ⟨q, p⟩ else none
        else none)

def makeVecs (size start : Idx₂) : List (Idx₂ × Idx₂) := (makeNeighbors size start).map ((start, ·))

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

def startPosition (self : Rect Circuit) : Idx₂ := self.findPosition? (· == Circuit.s) |>.unwrapOr (0, 0)

def dest (mat : Rect Circuit) (vec : Vec₂ × Vec₂) : Vec₂ × Vec₂ :=
  let (pre, now) := vec
  let dy := now.fst - pre.fst
  let dx := now.snd - pre.snd
  if p : (0, 0) ≤ now
  then
    let now' : Idx₂ := ⟨now, p⟩
    let next := match mat.get? now' with
      | some .v => (now.fst + dy, now.snd)
      | some .h => (now.fst     , now.snd + dx)
      | some .l => (now.fst + dx, now.snd + dy)
      | some .j => (now.fst - dx, now.snd - dy)
      |       _ => now
    (now, next)
  else ((0, 0), (0, 0))

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := pchar '|' <|> pchar '-' <|> pchar 'L' <|> pchar 'J' <|> pchar '7' <|> pchar 'F' <|> pchar '.' <|> pchar 'S'

def parse := AoCParser.parse parser
  where
    pcircuit := (return Circuit.ofChar) <*> cell
    parser := (return Rect.of2DMatrix) <*> many (many pcircuit <* eol)

end parser

namespace part1

def loop_len (self : Rect Circuit) (limit : Nat) (start : Idx₂) (len : Nat) (vec : Idx₂ × Idx₂) : Nat :=
  match limit with
  | 0        => 0
  | lim' + 1 =>
    let v' := dest self (vec.fst, vec.snd)
    if v'.fst.fst == v'.snd.fst && v'.fst.snd == v'.snd.snd
      then if v'.snd.fst == start.fst && v'.snd.snd == start.snd then len + 1 else 0
      else if p : (0, 0) ≤ v'.fst && (0, 0) ≤ v'.snd
      then
        let v'₁ : Idx₂ := ⟨v'.fst, by simp at p; obtain ⟨p1, _⟩ := p; exact p1⟩
        let v'₂ : Idx₂ := ⟨v'.snd, by simp at p; obtain ⟨_, p2⟩ := p; exact p2⟩
        loop_len self lim' start (len + 1) (v'₁, v'₂)
      else
        panic "impossible"

def solve (m : Rect Circuit) : Nat :=
  makeVecs (m.vector.size / m.width, m.width) (startPosition m)
    |>.map (loop_len m m.area (startPosition m) 0 ·)
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

def map_of (size : Idx₂) (locs : List Idx₂) : Array PropagateState :=
  locs.foldl
    (fun map pos ↦ map.set! (size.snd * pos.fst + pos.snd).toNat PropagateState.Wall)
    (Array.replicate (size.fst.toNat * size.snd.toNat) PropagateState.Unknown)

def expand (self : Array PropagateState) (size : Idx₂) (n : Nat) : Array PropagateState :=
  if p : (0, 0) ≤ (n / size.snd, n % size.snd)
  then
    let s : Idx₂ := ⟨(n / size.snd, n % size.snd), p⟩
    makeNeighbors size s
      |>.foldl
        (fun m q ↦ match m[(size.snd * q.fst + q.snd).toNat]! with
          | .Unknown => m.set! (size.snd * q.fst + q.snd).toNat .ToExpand
          | _ => m)
        (self.set! n .Propagated)
  else
    self

/-
- Switch to 1D scan from 28 scan
-- #eval List.iota 4 |>.mapIdx fun i x ↦ (i, x)
-/
partial
def loop (m : Array PropagateState) (size : Idx₂) : Array PropagateState :=
  let r := m.foldl
    (fun (i, m, u) p ↦ ( i + 1, if p == PropagateState.ToExpand then (expand m size i, true) else (m, u)))
    (0, m, false)
  if r.snd.snd then loop r.snd.fst size else r.snd.fst

def propagate (self : Array PropagateState) (size : Idx₂) : Array PropagateState := loop s size
  where
    s := self.set! 0 .ToExpand

def mkLoop (self : Rect Circuit) (limit : Nat) (start : Idx₂) (path : List Idx₂) (vec : Vec₂ × Vec₂) : List Idx₂ :=
  match limit with
  | 0        => []
  | lim' + 1 =>
    let v'v := dest self vec
    let v1 : Idx₂ := if p : (0, 0) ≤ v'v.fst then ⟨v'v.fst, p⟩ else ⟨(0, 0), by decide⟩
    let v2 : Idx₂ := if p : (0, 0) ≤ v'v.snd then ⟨v'v.snd, p⟩ else ⟨(0, 0), by decide⟩
    if v1.fst == v2.fst && v1.snd == v2.snd
      then if v2.fst == start.fst && v2.snd == start.snd then path ++ [v1] else []
      else mkLoop self lim' start (path ++ [v1]) (v1, v2)

def interpolate (p : Vec₂) (q : Vec₂) : Vec₂ :=
  let (p', q') := both (fun d ↦ (d.fst * 2, d.snd * 2)) (p, q)
  ((p'.fst + q'.fst) / 2, (p'.snd + q'.snd) / 2)

-- #eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Vec₂ → List Vec₂
  | []          => []
  | p :: []     => [(p.fst * 2, p.snd * 2)]
  | p :: q :: l => ([(p.fst * 2, p.snd * 2), interpolate p q] : List Vec₂) ++ scaleUp (q :: l)

/-!
  1. pick the looping route
  2. double the scale
  3. draw the loop
  4. run propagation
  5. count the unmarked cells
-/
def solve (m: Rect Circuit) : Nat :=
  let st := startPosition m
  let shape : Idx₂ := ↑(m.vector.size / m.width, m.width)
  let loop := makeVecs shape st
    |>.map (fun v ↦ mkLoop m m.area st [st] ((↑v.fst : Vec₂), (↑v.snd : Vec₂)))
    |>.map (·.map (fun v ↦ v.1))
    |>.foldl (fun best cand ↦ if best.length < cand.length then cand else best) []
    |> scaleUp
    |>.flatMap (fun (v : Vec₂) ↦ [if p : (0, 0) ≤ v then ⟨v, p⟩ else ⟨(0, 0), by decide⟩])
  let size : Idx₂ := ⟨(shape.fst * 2, shape.snd * 2), by
    constructor
    · simp ; exact Int.zero_le_ofNat ((m.vector.size / m.width, m.width).fst * 2)
    · simp ; exact Int.zero_le_ofNat ((m.vector.size / m.width, m.width).snd * 2)
  ⟩
  let a_map := propagate (map_of size loop) size
  List.range shape.fst.toNat
    |>.foldl (fun sum y ↦
      List.range shape.snd.toNat
        |>.filter (fun x ↦ PropagateState.Unknown == a_map[size.snd.toNat * y * 2 + x * 2]!)
        |>.length
        |> (· + sum))
      0

end part2

public def solve := AocProblem.config 2023 10 (parser.parse · |>.join) part1.solve part2.solve

end Y2023.Day10
