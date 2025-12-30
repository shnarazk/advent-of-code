module

public import Batteries.Data.BinaryHeap
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

namespace Y2023.Day17

open CiCL
open Dim2

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
def parse : String → Option (Rect Nat) := AoCParser.parse parse₁
  where
    parse₁ := pure ∘ Rect.of2DMatrix =<< matrix

end parser

structure State where
  pos   : Idx₂
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
  let go_n (t : Nat) := if p : t ≤ limit && (0, 0) ≤ (state.pos.fst - 1, state.pos.snd)
    then
      let p : Idx₂ := ⟨(state.pos.fst - 1, state.pos.snd), by simp at p; obtain ⟨_, p2⟩ := p; exact le_of_le_of_eq p2 rfl⟩
      some <| State.mk p Dir.N (state.cost + r.get p 1) t
    else none
  let go_s (t : Nat) := if p : t ≤ limit && state.pos.fst < h && (0,0) ≤ (state.pos.fst + 1, state.pos.snd)
    then
      let p : Idx₂ := ⟨(state.pos.fst + 1, state.pos.snd), by simp at p; obtain ⟨_, p2⟩ := p; exact le_of_le_of_eq p2 rfl⟩
      some <| State.mk p Dir.S (state.cost + r.get p 1) t
    else none
  let go_w (t : Nat) := if p : t ≤ limit && 0 < state.pos.snd && (0, 0) ≤ (state.pos.fst, state.pos.snd - 1)
    then
      let p : Idx₂ := ⟨(state.pos.fst, state.pos.snd - 1), by simp at p; obtain ⟨_, p2⟩ := p; exact le_of_le_of_eq p2 rfl⟩
      some <| State.mk p Dir.W (state.cost + r.get p 1) t
    else none
  let go_e (t : Nat) := if p : t ≤ limit && state.pos.snd < w && (0, 0) ≤ (state.pos.fst, state.pos.snd + 1)
    then
      let p : Idx₂ := ⟨(state.pos.fst, state.pos.snd + 1), by simp at p; obtain ⟨_, p2⟩ := p; exact le_of_le_of_eq p2 rfl⟩
      some <| State.mk p Dir.E (state.cost + r.get p 1) t
    else none
  match state.dir with
  | .N => [go_n (state.steps + 1), go_e 1, go_w 1].filterMap I
  | .E => [go_e (state.steps + 1), go_s 1, go_n 1].filterMap I
  | .S => [go_s (state.steps + 1), go_e 1, go_w 1].filterMap I
  | .W => [go_w (state.steps + 1), go_s 1, go_n 1].filterMap I

variable (visited : Std.HashSet State)
variable (to_visit : List State)

partial
def find {f : State → State → Bool} (r : Rect Nat) (goal : Idx₂) (thr : Nat)
    (visited : Std.HashMap (Idx₂ × Dir) (Nat × Nat)) (to_visit :BinaryHeap f) : Nat :=
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
  find r (r.height - 1, r.width - 1) 1000000 Std.HashMap.emptyWithCapacity
    (#[State.mk (0, 0) Dir.E 0 0, State.mk (0, 0) Dir.S 0 0].toBinaryHeap
      (fun (b a : State) ↦ a.cost + path_len - (a.pos.fst + a.pos.snd)
        < b.cost + path_len - (b.pos.fst + b.pos.snd)))

end Part1

namespace Part2

def limitₗ := 10
def limitₛ := 4

def next_states (r : Rect Nat) (state : State) : List State :=
  let h := r.height - 1
  let w := r.width - 1
  let go_n (turn : Bool) (t : Nat) :=
    if p : (!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && (0, 0) ≤ (state.pos.fst - 1, state.pos.snd)
    then
      let q : Idx₂ := ⟨(state.pos.fst - 1, state.pos.snd), by simp at p; obtain ⟨_, p2⟩ := p; exact le_of_le_of_eq p2 rfl⟩
      some <| State.mk q Dir.N (state.cost + r.get q 1) t
    else none
  let go_s (turn : Bool) (t : Nat) :=
    if p : (!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && state.pos.fst < h && (0, 0) ≤ (state.pos.fst + 1, state.pos.snd)
    then
      let q : Idx₂ := ⟨(state.pos.fst + 1, state.pos.snd), by simp at p; obtain ⟨_, p2⟩ := p; exact p2⟩
      some <| State.mk q Dir.S (state.cost + r.get q 1) t
    else none
  let go_w (turn : Bool) (t : Nat) :=
    if p : (!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && 0 < state.pos.snd && (0, 0) ≤ (state.pos.fst, state.pos.snd - 1)
    then
      let q : Idx₂ := ⟨(state.pos.fst, state.pos.snd - 1), by simp at p; obtain ⟨_, p2⟩ := p; exact p2⟩
      some <| State.mk q Dir.W (state.cost + r.get q 1) t
    else none
  let go_e (turn : Bool) (t : Nat) :=
    if p : (!turn || limitₛ ≤ state.steps) && t ≤ limitₗ && state.pos.snd < w && (0, 0) ≤ (state.pos.fst, state.pos.snd + 1)
    then
      let q : Idx₂ := ⟨(state.pos.fst, state.pos.snd + 1), by simp at p; obtain ⟨_, p2⟩ := p; exact p2⟩
      some <| State.mk q Dir.E (state.cost + r.get q 1) t
    else none
  match state.dir with
  | .N => [go_n false (state.steps + 1), go_e true 1, go_w true 1].filterMap I
  | .E => [go_e false (state.steps + 1), go_s true 1, go_n true 1].filterMap I
  | .S => [go_s false (state.steps + 1), go_e true 1, go_w true 1].filterMap I
  | .W => [go_w false (state.steps + 1), go_s true 1, go_n true 1].filterMap I

variable (visited : Std.HashSet State)
variable (to_visit : List State)

partial
def find {f : State → State → Bool} (r : Rect Nat) (goal : Idx₂) (thr : Nat)
    (visited : Std.HashMap (Idx₂ × Dir × Nat) Nat) -- (y, x) × dir × stepsₛ → cost
    (to_visit :BinaryHeap f) : Nat :=
  if let (some state, to_visit') := to_visit.extractMax then
    if state.pos.fst == goal.fst && state.pos.snd == goal.snd && limitₛ ≤ state.steps then
      if limitₛ ≤ state.steps then
        state.cost
      else
        find r goal thr visited to_visit'
    else
      let costᵣ := visited.getD (state.pos, state.dir, state.steps) 100000
      if thr <= state.cost || costᵣ <= state.cost then
        find r goal thr visited to_visit'
      else
        let states := next_states r state
            |>.filter (fun s ↦ s.cost < visited.getD (s.pos, s.dir, s.steps) 100000)
        find r goal thr
          (visited.insert (state.pos, state.dir, state.steps) state.cost)
          (states.foldl (·.insert ·) to_visit')
  else
    thr

def solve (r : Rect Nat) : Nat :=
  let path_len := 10 * (r.height + r.width)
  find r (r.height - 1, r.width - 1) 1000000 Std.HashMap.emptyWithCapacity
    (#[State.mk (0, 0) Dir.E 0 0, State.mk (0, 0) Dir.S 0 0].toBinaryHeap
      (fun (b a : State) ↦ a.cost + path_len - (a.pos.fst + a.pos.snd)
        < b.cost + path_len - (b.pos.fst + b.pos.snd)))

end Part2

public def solve := AocProblem.config 2023 17 parser.parse Part1.solve Part2.solve

end Y2023.Day17
