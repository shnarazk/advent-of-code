import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2023.Day17

open Accumulation CiCL
open TwoDimensionalVector64

structure Input where
deriving BEq, Repr

instance : ToString Input where toString _ := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line : Parser (Array Nat) := do
  let l ← many1 digit <* eol
  return l.map (fun (c : Char) ↦ (c.val - '0'.val).toNat)

def matrix := many1 line
def parse : String → Option (Rect Nat) := AoCParser.parse parse
  where
    parse := pure ∘ Rect.of2DMatrix =<< matrix

end parser

abbrev State := Dim2 × Dir × Nat

def next_states (r : Rect Nat) (state : State) : List State :=
  let (pos, dir, turn) := state
  let h := r.height
  let w := r.width
  let limit := 2
  let go_n (t : Nat) := (t < limit && 0 < pos.fst).map
      (K ((pos.fst - 1, pos.snd), Dir.N, t))
  let go_s (t : Nat) := (t < limit && pos.fst < h - 1).map
      (K ((pos.fst + 1, pos.snd), Dir.S, t))
  let go_w (t : Nat) := (t < limit && 0 < pos.snd    ).map
      (K ((pos.fst, pos.snd - 1), Dir.W, t))
  let go_e (t : Nat) := (t < limit && pos.snd < w - 1).map
      (K ((pos.fst, pos.snd + 1), Dir.E, t))
  match dir with
  | .N => [go_n (turn + 1), go_e 0, go_w 0] |>.filterMap I
  | .E => [go_e (turn + 1), go_n 0, go_s 0] |>.filterMap I
  | .S => [go_s (turn + 1), go_w 0, go_e 0] |>.filterMap I
  | .W => [go_w (turn + 1), go_s 0, go_n 0] |>.filterMap I

namespace Part1

variable (visited : Std.HashSet State)
variable (to_visit : List State)

partial def find (r : Rect Nat) (vt : Std.HashSet State × List State) : Nat :=
  let (visited, to_visit) := vt
  match to_visit with
  | [] => r.get (r.height - 1) r.width 0
  | (pos, _dist) :: to_visit' =>
    let _w := r.get pos.fst pos.snd 0
    find r (visited, to_visit')

def solve (r : Rect Nat) : Nat := 0

end Part1

namespace Part2

def solve (_ : Rect Nat) : Nat := 0

end Part2

def solve := AocProblem.config 2023 17 parser.parse Part1.solve Part2.solve

end Y2023.Day17
