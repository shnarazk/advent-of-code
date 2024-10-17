import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect

def dbg {α : Type} [ToString α] (a : α) : α := dbgTrace s!"{a}" (fun _ ↦ a)

namespace Option

/--
- `(some "abc").mapOr (·.length) 99 => 3`
- `none.mapOr (·.length) 99 => 99`

`map_or` is already used for a prep
-/
def mapOr {α β : Type} : (Option α) → (f : α → β) → (default : β) → β
  | (some a), f, _ => f a
  | none, _, default => default

end Option

-- #eval some "abc" |>.mapOr (·.length) 99
-- #eval none |>.mapOr (·.length) 99

namespace Dim2

def cutsₕ (g : Dim2) : List Nat := List.range g.y.toNat |>.drop 1
def cutsᵥ (g : Dim2) : List Nat := List.range g.x.toNat |>.drop 1

-- #eval (Dim2.mk 3 1).cutsₕ

end Dim2

namespace TwoDimensionalVector.Rect

variable (r : Rect Bool)

def mirroredₕ (p : Dim2) (h : Nat) : Option Dim2 :=
  if p.y < h then
    let y' := h + h - p.y - 1
    if y' < r.shape.y then some { p with y := y' } else none
  else
    let y' := p.y - h
    if h < y' then none else some { p with y := h - y' - 1 }

def r99 := Rect.ofDim2 (Dim2.mk 9 9) (by simp [NonNegDim]) false
def p := Dim2.mk 1 5
-- #eval r99.mirroredₕ p 2
-- #eval if let some q := r99.mirroredₕ p 2 then r99.mirroredₕ q 2 else none

-- #eval mirrored_horizontally r99 (Dim2.mk 4 5) 4

def mirroredᵥ (p : Dim2) (v : Nat) : Option Dim2 :=
  if p.x < v then
    let x' := v + v - p.x - 1
    if x' < r.shape.x then some { p with x := x' } else none
  else
    let x' := p.x - v
    if v < x' then none else some { p with x := v - x' - 1 }

-- #eval r99.mirroredᵥ (Dim2.mk 4 5) 4

def cutₕ (n : Nat) : Option Nat :=
  -- 対応するものがなければ `true`
  if r.shape.toList.all (fun p ↦ r.mirroredₕ p n |>.mapOr (r.get p false = r.get · false) true) then
    some (n * 100)
  else
    none

-- #eval r99.cutₕ 1
-- #eval r99.get (Dim2.mk 1 1) true = r99.get (Dim2.mk 1 2) true

def cutᵥ (n : Nat) : Option Nat :=
  if r.shape.toList.all (fun p ↦ r.mirroredᵥ p n |>.mapOr (r.get p false = r.get · false) true) then
    some n
  else
    none

-- #eval r99.cutᵥ 1

def find_cutₕ : Nat := r.shape.cutsₕ.foldl (fun acc k ↦ r.cutₕ k |>.mapOr (· + acc) acc) 0
def find_cutᵥ : Nat := r.shape.cutsᵥ.foldl (fun acc k ↦ r.cutᵥ k |>.mapOr (· + acc) acc) 0
def evaluate : Nat := r.find_cutₕ + r.find_cutᵥ

-- #eval r99.evaluate

end TwoDimensionalVector.Rect

namespace Y2023.Day13

open Std Accumulation CoP CiCL
open TwoDimensionalVector

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def maze_line := do
  let v ← many1 ((pchar '.').orElse fun _ ↦ pchar '#') <* eol
  return v.map (· == '#')

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Bool)) := AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1

def solve (pls : Array (Rect Bool)) : Nat := pls.map (·.evaluate) |> sum

end Part1

namespace Part2

def solve (_ : Array (Rect Bool)) : Nat := 0

end Part2

-- #eval (some #[3, 5]).map (·.shrink 1)

def solve := AocProblem.config 2023 13
  parser.parse
  -- ((·.map ((⎊toString‿dbgTrace‿K) ∘ (·.shrink 1))) ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day13
