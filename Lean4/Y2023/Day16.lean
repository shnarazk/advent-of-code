module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

open Accumulation CiCL Dim2

namespace Y2023.Day16

inductive Kind where | V | H | S | B | E | P deriving BEq, Hashable, Repr

instance : ToString Kind where
  toString : Kind → String
    | .V => "|"
    | .H => "-"
    | .S => "/"
    | .B => "\\"
    | .E => "."
    | .P => "ω"

instance : ToString (Rect Kind) where
  toString (r : Rect Kind) : String :=
    r.to2Dmatrix.map (fun l ↦ l.map toString |> String.join)
      |>.map (· ++ "\n")
      |>String.join
      |>("\n" ++ ·)

inductive Dir where | N | E | S | W deriving BEq, Hashable, Repr

def propagate (r : Rect Kind) (pos : Idx₂) (dir : Dir) : List (Idx₂ × Dir) :=
  let k := r.get pos Kind.E
  let w := r.width - 1
  let h := r.height - 1
  let go_n := (0 < pos.fst : Bool).map (K ((pos.fst - 1, pos.snd), Dir.N))
  let go_e := (pos.snd < w : Bool).map (K ((pos.fst, pos.snd + 1), Dir.E))
  let go_s := (pos.fst < h : Bool).map (K ((pos.fst + 1, pos.snd), Dir.S))
  let go_w := (0 < pos.snd : Bool).map (K ((pos.fst, pos.snd - 1), Dir.W))
  let toIdx := fun (p, d) ↦ (if h : (0,0) ≤ p then let q : Idx₂ := ⟨p, h⟩; q else ⟨(0, 0), by decide⟩, d)
  match dir, k with
    | Dir.N, Kind.V => [go_n]       |>.filterMap I |>.map toIdx
    | Dir.N, Kind.H => [go_e, go_w] |>.filterMap I |>.map toIdx
    | Dir.N, Kind.S => [go_e]       |>.filterMap I |>.map toIdx
    | Dir.N, Kind.B => [go_w]       |>.filterMap I |>.map toIdx
    | Dir.N, Kind.E => [go_n]       |>.filterMap I |>.map toIdx

    | Dir.E, Kind.V => [go_n, go_s] |>.filterMap I |>.map toIdx
    | Dir.E, Kind.H => [go_e]       |>.filterMap I |>.map toIdx
    | Dir.E, Kind.S => [go_n]       |>.filterMap I |>.map toIdx
    | Dir.E, Kind.B => [go_s]       |>.filterMap I |>.map toIdx
    | Dir.E, Kind.E => [go_e]       |>.filterMap I |>.map toIdx

    | Dir.S, Kind.V => [go_s]       |>.filterMap I |>.map toIdx
    | Dir.S, Kind.H => [go_e, go_w] |>.filterMap I |>.map toIdx
    | Dir.S, Kind.S => [go_w]       |>.filterMap I |>.map toIdx
    | Dir.S, Kind.B => [go_e]       |>.filterMap I |>.map toIdx
    | Dir.S, Kind.E => [go_s]       |>.filterMap I |>.map toIdx

    | Dir.W, Kind.V => [go_n, go_s] |>.filterMap I |>.map toIdx
    | Dir.W, Kind.H => [go_w]       |>.filterMap I |>.map toIdx
    | Dir.W, Kind.S => [go_s]       |>.filterMap I |>.map toIdx
    | Dir.W, Kind.B => [go_n]       |>.filterMap I |>.map toIdx
    | Dir.W, Kind.E => [go_w]       |>.filterMap I |>.map toIdx

    | _, Kind.P => []

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := do
  let c ← pchar '|' <|> pchar '-' <|> pchar '\\' <|> pchar '/' <|> pchar '.'
  return match c with
    | '|' => Kind.V
    | '-' => Kind.H
    | '/' => Kind.S
    | '\\' => Kind.B
    | _   => Kind.E

def maze_line := many1 cell <* eol
def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix
def parse : String → Option (Array (Rect Kind)) := AoCParser.parse (separated maze eol)

end parser

def injectTrace (self : Rect Kind) (visited : Std.HashSet (Idx₂ × Dir)) : Rect Kind :=
  visited.toList.foldl (fun r (p, _) ↦ r.set p Kind.P) self

partial
def traverse (r : Rect Kind) (visited : Std.HashSet (Idx₂ × Dir)) (to_visit : List (Idx₂ × Dir))
    : Rect Kind :=
  if to_visit.isEmpty then
    injectTrace r visited
  else
    to_visit.foldl
        (fun (v, t) posDir ↦
          if v.contains posDir then
            (v, t)
          else
            let l := uncurry (propagate r) posDir |>.filter (!t.contains ·)
            (v.insert posDir, l ++ t))
        (visited, [])
      |> uncurry (traverse r)

def evaluate (r : Rect Kind) (start : (Idx₂ × Dir)): Nat :=
  traverse r Std.HashSet.emptyWithCapacity [start]
    |>.vector
    |>.filter (· == Kind.P)
    |>.size

namespace Part1

def solve (rs : Array (Rect Kind)) : Nat :=
  rs.map (evaluate · ((0, 0), Dir.E)) |> sum

end Part1

namespace Part2

def maximize (r : Rect Kind) : Nat :=
  let w := r.width
  let h := r.height
  let n := range_list w |>.map (fun x ↦ (((0 : Int), x), Dir.S))
  let s := range_list w |>.map (fun x ↦ (((h : Int) - 1, x), Dir.N))
  let e := range_list h |>.map (fun y ↦ ((y, (0 : Int)), Dir.S))
  let w := range_list h |>.map (fun y ↦ ((y, (w : Int) - 1), Dir.S))
  (n ++ s ++ e ++ w)
    |>.flatMap (fun (p,d) ↦ if h : (0, 0) ≤ p then let q : Idx₂ := ⟨p, h⟩ ; [(q, d)] else [])
    |>.map (evaluate r ·)
    |>.max?
    |>.unwrapOr 0

def solve (rs : Array (Rect Kind)) : Nat := rs.map maximize |> sum

end Part2

public def solve := AocProblem.config 2023 16 parser.parse Part1.solve Part2.solve

end Y2023.Day16
