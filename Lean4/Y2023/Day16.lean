import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

open Accumulation CiCL TwoDimensionalVector64

def Bool.map {α : Type} (self : Bool) (f : Unit → α) : Option α :=
  match self with
  | true  => some (f ())
  | false => none
-- #eval true.map (K 3)

namespace Y2023.Day16

inductive Kind where
| V | H | S | B | E
deriving BEq, Hashable, Repr

instance : ToString Kind where
  toString : Kind → String
    | .V => "|"
    | .H => "-"
    | .S => "/"
    | .B => "\\"
    | .E => "."

instance : ToString (Rect Kind) where
  toString (r : Rect Kind) : String :=
    r.to2Dmatrix.map (fun l ↦ l.map toString |> String.join)
      |>.map (· ++ "\n")
      |>String.join

inductive Dir where
| N | E | S | W
deriving BEq, Hashable, Repr

-- #eval [some 3, none, some 2] |>.filterMap I

def propagate (r : Rect Kind) (pos : Dim2) (dir : Dir) : List (Dim2 × Dir) :=
  let k := r.get pos.fst pos.snd Kind.E
  let w := r.width
  let h := r.height
  let go_n := (0 < pos.fst : Bool).map (K ((pos.fst - 1, pos.snd), dir))
  let go_e := (pos.snd < w : Bool).map (K ((pos.fst, pos.snd + 1), dir))
  let go_s := (pos.fst < h : Bool).map (K ((pos.fst + 1, pos.snd), dir))
  let go_w := (0 < pos.snd : Bool).map (K ((pos.fst, pos.snd - 1), dir))
  match dir, k with
    | Dir.N, Kind.V => [go_n]       |>.filterMap I
    | Dir.N, Kind.H => [go_e, go_w] |>.filterMap I
    | Dir.N, Kind.S => [go_e]       |>.filterMap I
    | Dir.N, Kind.B => [go_w]       |>.filterMap I
    | Dir.N, Kind.E => [go_n]       |>.filterMap I

    | Dir.E, Kind.V => [go_n, go_s] |>.filterMap I
    | Dir.E, Kind.H => [go_e]       |>.filterMap I
    | Dir.E, Kind.S => [go_n]       |>.filterMap I
    | Dir.E, Kind.B => [go_s]       |>.filterMap I
    | Dir.E, Kind.E => [go_e]       |>.filterMap I

    | Dir.S, Kind.V => [go_s]       |>.filterMap I
    | Dir.S, Kind.H => [go_e, go_w] |>.filterMap I
    | Dir.S, Kind.S => [go_w]       |>.filterMap I
    | Dir.S, Kind.B => [go_e]       |>.filterMap I
    | Dir.S, Kind.E => [go_s]       |>.filterMap I

    | Dir.W, Kind.V => [go_n, go_s] |>.filterMap I
    | Dir.W, Kind.H => [go_w]       |>.filterMap I
    | Dir.W, Kind.S => [go_s]       |>.filterMap I
    | Dir.W, Kind.B => [go_n]       |>.filterMap I
    | Dir.W, Kind.E => [go_w]       |>.filterMap I

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

def parse : String → Option (Array (Rect Kind)) := AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1

partial def traverse (r : Rect Kind) (visited : Std.HashSet (Dim2 × Dir)) (to_visit : List (Dim2 × Dir))
    : Std.HashSet (Dim2 × Dir) :=
  if to_visit.isEmpty then
    dbgTrace s!"{visited.toList |>.map (·.fst)}" (K visited)
  else
    to_visit.foldl
        (fun (v, t) posDir ↦
          let v' := v.insert posDir
          let l := uncurry (propagate r) posDir |>.filter (!t.contains ·)
          (v', l++t))
        (visited, [])
      |> uncurry (traverse r)

def solve (rs : Array (Rect Kind)) : Nat :=
  rs.map (traverse · Std.HashSet.empty [((0, 0), Dir.E)] |>.size) |> sum

end Part1

namespace Part2

def solve (_ : Array (Rect Kind)) : Nat := 0

end Part2

def solve := AocProblem.config 2023 16
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day16
