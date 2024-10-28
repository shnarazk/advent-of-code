import Batteries.Data.BinaryHeap
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

structure State where
  pos   : Dim2
  dir   : Dir
  cost  : Nat
  steps : Nat
  deriving BEq, Hashable

instance : ToString State where
  toString s := s!"<({s.pos.fst}, {s.pos.snd}){s.dir} c:{s.cost} #{s.steps}>"

abbrev BinaryHeap := Batteries.BinaryHeap State

namespace Part1

def limit := 3

def next_states (r : Rect Nat) (state : State) : List State :=
  let h := r.height - 1
  let w := r.width - 1
  let go_n (t : Nat) := (t ≤ limit && 0 < state.pos.fst).map
      (fun _ ↦ let p := (state.pos.fst - 1, state.pos.snd)
          State.mk p Dir.N (state.cost + r.get p.fst p.snd 1) t)
  let go_s (t : Nat) := (t ≤ limit && state.pos.fst < h).map
      (fun _ ↦ let p := (state.pos.fst + 1, state.pos.snd)
          State.mk p Dir.S (state.cost + r.get p.fst p.snd 1) t)
  let go_w (t : Nat) := (t ≤ limit && 0 < state.pos.snd).map
      (fun _ ↦ let p := (state.pos.fst, state.pos.snd - 1)
          State.mk p Dir.W (state.cost + r.get p.fst p.snd 1) t)
  let go_e (t : Nat) := (t ≤ limit && state.pos.snd < w).map
      (fun _ ↦ let p := (state.pos.fst, state.pos.snd + 1)
          State.mk p Dir.E (state.cost + r.get p.fst p.snd 1) t)
  match state.dir with
  | .N => [go_n (state.steps + 1), go_e 1, go_w 1].filterMap I
  | .E => [go_e (state.steps + 1), go_s 1, go_n 1].filterMap I
  | .S => [go_s (state.steps + 1), go_e 1, go_w 1].filterMap I
  | .W => [go_w (state.steps + 1), go_s 1, go_n 1].filterMap I

variable (visited : Std.HashSet State)
variable (to_visit : List State)

partial def find {f : State → State → Bool} (r : Rect Nat) (goal : Dim2) (thr : Nat)
    (visited : Std.HashMap (Dim2 × Dir) (Nat × Nat)) (to_visit :BinaryHeap f) : Nat :=
  if let (some state, to_visit') := to_visit.extractMax then
    if state.pos.fst == goal.fst && state.pos.snd == goal.snd then
      state.cost
    else
      let recorded := visited.getD (state.pos, state.dir) (100000, 10)
      let not_covered := state.cost < recorded.fst || state.steps < recorded.snd
      if thr <= state.cost || !not_covered then
        find r goal thr visited to_visit'
      else
        let states := next_states r state
            |>.filter (fun s ↦
                let recorded := visited.getD (s.pos, s.dir) (100000, 10)
                s.cost < recorded.fst || s.steps < recorded.snd)
        find r goal thr
          (visited.insert (state.pos, state.dir) (state.cost, state.steps))
          (states.foldl (·.insert ·) to_visit')
  else
    thr

def solve (r : Rect Nat) : Nat :=
  let path_len := 10 * (r.height + r.width)
  find r (r.height - 1, r.width - 1) 1000000 Std.HashMap.empty
    (#[State.mk (0, 0) Dir.E 0 0, State.mk (0, 0) Dir.S 0 0].toBinaryHeap
      (fun (b a : State) ↦ a.cost.toUInt64 + path_len - (a.pos.fst + a.pos.snd)
        < b.cost.toUInt64 + path_len - (b.pos.fst + b.pos.snd)))

end Part1

namespace Part2

def limitₗ := 10
def limitₛ := 4

def next_states (r : Rect Nat) (state : State) : List State :=
  let h := r.height - 1
  let w := r.width - 1
  let go_n (turn : Bool) (t : Nat) :=
    ((!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && 0 < state.pos.fst).map
      (fun _ ↦ let p := (state.pos.fst - 1, state.pos.snd)
          State.mk p Dir.N (state.cost + r.get p.fst p.snd 1) t)
  let go_s (turn : Bool) (t : Nat) :=
    ((!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && state.pos.fst < h).map
      (fun _ ↦ let p := (state.pos.fst + 1, state.pos.snd)
          State.mk p Dir.S (state.cost + r.get p.fst p.snd 1) t)
  let go_w (turn : Bool) (t : Nat) :=
    ((!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && 0 < state.pos.snd).map
      (fun _ ↦ let p := (state.pos.fst, state.pos.snd - 1)
          State.mk p Dir.W (state.cost + r.get p.fst p.snd 1) t)
  let go_e (turn : Bool) (t : Nat) :=
    ((!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && state.pos.snd < w).map
      (fun _ ↦ let p := (state.pos.fst, state.pos.snd + 1)
          State.mk p Dir.E (state.cost + r.get p.fst p.snd 1) t)
  match state.dir with
  | .N => [go_n false (state.steps + 1), go_e true 1, go_w true 1].filterMap I
  | .E => [go_e false (state.steps + 1), go_s true 1, go_n true 1].filterMap I
  | .S => [go_s false (state.steps + 1), go_e true 1, go_w true 1].filterMap I
  | .W => [go_w false (state.steps + 1), go_s true 1, go_n true 1].filterMap I

variable (visited : Std.HashSet State)
variable (to_visit : List State)

partial def find {f : State → State → Bool} (r : Rect Nat) (goal : Dim2) (thr : Nat)
    (visited : Std.HashMap (Dim2 × Dir) (Nat × Nat)) (to_visit :BinaryHeap f) : Nat :=
  if let (some state, to_visit') := to_visit.extractMax then
    if state.pos.fst == goal.fst && state.pos.snd == goal.snd then
      state.cost
    else
      let recorded := visited.getD (state.pos, state.dir) (100000, 10)
      let not_covered := state.cost < recorded.fst || state.steps < recorded.snd
      if thr <= state.cost || !not_covered then
        find r goal thr visited to_visit'
      else
        let states := next_states r state
            |>.filter (fun s ↦
                let recorded := visited.getD (s.pos, s.dir) (100000, 10)
                s.cost < recorded.fst || s.steps < recorded.snd)
        find r goal thr
          (visited.insert (state.pos, state.dir) (state.cost, state.steps))
          ((dbg "" states).foldl (·.insert ·) to_visit')
  else
    thr

def solve (r : Rect Nat) : Nat :=
  let path_len := 10 * (r.height + r.width)
  find r (r.height - 1, r.width - 1) 1000000 Std.HashMap.empty
    (#[State.mk (0, 0) Dir.E 0 0, State.mk (0, 0) Dir.S 0 0].toBinaryHeap
      (fun (b a : State) ↦ a.cost.toUInt64 + path_len - (a.pos.fst + a.pos.snd)
        < b.cost.toUInt64 + path_len - (b.pos.fst + b.pos.snd)))

end Part2

def solve := AocProblem.config 2023 17 parser.parse Part1.solve Part2.solve

end Y2023.Day17
