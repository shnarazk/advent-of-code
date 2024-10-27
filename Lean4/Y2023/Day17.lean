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

/--
Composition : location × total cost × direction × steps toward the current direction
-/
abbrev State := Dim2 × Nat × Dir × Nat

def next_states (r : Rect Nat) (state : State) : List State :=
  let (pos, cost, dir, turn) := state
  let h := r.height
  let w := r.width
  let limit := 2
  let go_n (t : Nat) := (t < limit && 0 < pos.fst).map
      (fun _ ↦ let p := (pos.fst - 1, pos.snd)
          (p, cost + r.get p.fst p.snd 0, Dir.N, t))
  let go_s (t : Nat) := (t < limit && pos.fst < h - 1).map
      (fun _ ↦ let p := (pos.fst + 1, pos.snd)
          (p, cost + r.get p.fst p.snd 0, Dir.S, t))
  let go_w (t : Nat) := (t < limit && 0 < pos.snd    ).map
      (fun _ ↦ let p := (pos.fst, pos.snd - 1)
          (p, cost + r.get p.fst p.snd 0, Dir.W, t))
  let go_e (t : Nat) := (t < limit && pos.snd < w - 1).map
      (fun _ ↦ let p := (pos.fst, pos.snd + 1)
          (p, cost + r.get p.fst p.snd 0, Dir.E, t))
  match dir with
  | .N => [go_n (turn + 1), go_e 0, go_w 0] |>.filterMap I
  | .E => [go_e (turn + 1), go_s 0, go_n 0] |>.filterMap I
  | .S => [go_s (turn + 1), go_e 0, go_w 0] |>.filterMap I
  | .W => [go_w (turn + 1), go_s 0, go_n 0] |>.filterMap I

namespace Part1

variable (visited : Std.HashSet State)
variable (to_visit : List State)

partial def find (r : Rect Nat) (goal : Dim2) (thr : Nat) (vt : Std.HashSet State × List State) : Nat :=
  let (visited, to_visit) := vt
  match to_visit with
  | [] => thr
  | state@(pos, cost, _, _) :: to_visit' =>
    if pos == goal then
      if cost < thr then
        find r goal (dbg "new cost" cost) (visited, to_visit)
      else
          find r goal thr (visited, to_visit)
    else if thr <= cost || visited.contains state  then
      find r goal thr (visited, to_visit)
    else
      let states := next_states r state |>.filter (fun s ↦ !visited.contains s)
      find r goal thr (visited.insert state, states ++ to_visit')

def solve (r : Rect Nat) : Nat :=
  find r (r.height - 1, r.width - 1) 1000000
      (Std.HashSet.empty, [((0, 0), 0, Dir.E, 0)])

end Part1

namespace Part2

def solve (_ : Rect Nat) : Nat := 0

end Part2

def solve := AocProblem.config 2023 17 parser.parse Part1.solve Part2.solve

end Y2023.Day17
