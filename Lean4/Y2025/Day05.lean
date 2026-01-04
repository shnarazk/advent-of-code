module

public import WinnowParsers
public import «AoC».Basic

namespace Y2025.Day05

structure Input where
  ranges : Array (Nat × Nat)
  ids : Array Nat
deriving BEq, Repr

instance : ToString Input where toString s := s!"{s.ranges}, {s.ids}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec.String

def parse_range := do Prod.mk <$> (number <* (pchar '-')) <*> number
def parse_ids := separated number eol

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do Input.mk <$> ((separated parse_range eol) <* eol <* eol) <*> parse_ids

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.ids |>.filter (fun i ↦ input.ranges.iter.any (fun r ↦ r.fst ≤ i && i ≤ r.snd)) |>.size

end Part1

namespace Part2

open Std

instance : LT (Nat × Bool) where
  lt a b := a.fst < b.fst ∨ (a.fst = b.fst ∧ a.snd < b.snd)

instance : DecidableLT (Nat × Bool) := by
  intro p q
  have h1 : Decidable (p.fst < q.fst) := inferInstance
  have h2 : Decidable (p.fst = q.fst) := inferInstance
  have h3 : Decidable (p.snd < q.snd) := inferInstance
  have h4 : Decidable (p < q) :=
    match h1 with
    | isTrue hlt => isTrue (Or.inl hlt)
    | isFalse hnlt =>
      match h2 with
      | isTrue heq =>
        match h3 with
        | isTrue hlt2 => isTrue (Or.inr ⟨heq, hlt2⟩)
        | isFalse hnlt2 => isFalse (fun h ↦
            match h with
            | Or.inl hlt => absurd hlt hnlt
            | Or.inr ⟨_, hlt2⟩ => absurd hlt2 hnlt2)
      | isFalse hneq => isFalse (fun h ↦
          match h with
          | Or.inl hlt => absurd hlt hnlt
          | Or.inr ⟨heq', _⟩ => absurd heq' hneq)
  exact h4

#guard (2, true) < (3, false)

def solve (input : Input) : Nat := Id.run do
  let nodes : HashMap (Nat × Bool) Nat := input.ranges.foldl
    (fun acc range ↦ acc
      |>.alter (range.fst, false) (·.mapOr (· + 1) 1 |> some)
      |>.alter (range.snd, true) (·.mapOr (· + 1) 1 |> some))
    (HashMap.emptyWithCapacity (2 * input.ranges.size))
  let mut (level, start, total) := (0, 0, 0)
  for ((n, b), c) in nodes.toArray.qsort (·.fst < ·.fst) do
    if b
    then
      level := level - c
      if level == 0 then total := total + (n + 1 - start)
    else
      if level == 0 then start := n
      level := level + c
  total

end Part2

public def solve := AocProblem.config 2025 05 parser.parse Part1.solve Part2.solve

end Y2025.Day05
