module

public import WinnowParsers
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec

def cuts (g : Nat) : List Nat := List.range g |>.drop 1

namespace Dim2.Rect

variable (r : Rect Bool)

/-- vertically mirror point. So horizon is the base. -/
def mirroredₕ (p : Idx₂) (h' : Nat) : Option Idx₂ :=
  let h : Int := Int.ofNat h'
  if p.1 < h then
    let y' : Int := h + h - p.1 - 1
    if y' < r.height && 0 ≤ y' then some (y'.toNat, p.2) else none
  else
    let y' : Int := p.1 - h
    if h ≥ y' + 1 && 0 ≤ h - y' - 1 then some ((h - y' - 1).toNat, p.2) else none

-- def r99 := Rect.ofDim2 (Dim2.mk 5 6) (by simp [NonNegDim]) false
-- def p := Dim2.mk 1 5
-- #eval r99.mirroredₕ p 2
-- #eval if let some q := r99.mirroredₕ p 2 then r99.mirroredₕ q 2 else none
-- #eval mirroredₕ r99 (Dim2.mk 4 5) 2

/-- Return optinal Dim2 that locates on the horrizontally mirrored position. -/
def mirroredᵥ (p : Idx₂) (v' : Nat) : Option Idx₂ :=
  let v : Int := Int.ofNat v'
  if p.2 < v then
    let x' : Int := (v + v) - p.2 - 1
    if x' < r.width && 0 ≤ x' then some (p.1, x'.toNat) else none
  else
    let x' : Int := ((↑ p.2) : Int) - v
    if v ≥ x' + 1 && 0 ≤ v - x' - 1 then some (p.1, (v - x' - 1).toNat) else none

-- #eval r99.mirroredᵥ (Dim2.mk 4 5) 4

-- #eval r99.cutᵥ 1

end Dim2.Rect

namespace Y2023.Day13

open Accumulation CoP CiCL
open Dim2

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def maze_line := do
  let v ← many1 ((pchar '.').orElse fun _ ↦ pchar '#') <* eol
  return v.map (· == '#')

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Bool)) := AoCParser.parse parser
  where
    parser := separated maze eol

end parser

namespace Part1

variable (r : Rect Bool)

def cutₕ (r : Rect Bool) (n : Nat) : Option Nat :=
  -- 対応するものがなければ `true`
  if r.range.all (fun p ↦ r.mirroredₕ p n |>.mapOr (r[p]? = r[·]?) true) then
    some (n * 100)
  else
    none

-- #eval r99.cutₕ 1
-- #eval r99.get (Dim2.mk 1 1) true = r99.get (Dim2.mk 1 2) true

def cutᵥ (r : Rect Bool) (n : Nat) : Option Nat :=
  if r.range.all (fun p ↦ r.mirroredᵥ p n |>.mapOr (r[p]? = r[·]?) true) then
    some n
  else
    none

def find_cutₕ : Nat := cuts r.height |>.map (cutₕ r ·) |> sum
def find_cutᵥ : Nat := cuts r.width |>.map (cutᵥ r ·) |> sum
def evaluate : Nat := find_cutₕ r + find_cutᵥ r

-- #eval r99.evaluate

def solve (pls : Array (Rect Bool)) : Nat := pls.map evaluate |> sum

end Part1

namespace Part2

variable (r : Rect Bool)

def smudgedₕ (n : Nat) : Option Nat :=
  if r.range
      |>.map (fun p ↦ r.mirroredₕ p n |>.mapOr (r[p]? != r[·]?) false)
      |>.filter (·)
      |> (·.size = 2)
  then
    some (n * 100)
  else
    none

def smudgedᵥ (r : Rect Bool) (n : Nat) : Option Nat :=
  if r.range
    |>.map (fun p ↦ r.mirroredᵥ p n |>.mapOr (r[p]? != r[·]?) false)
    |>.filter (·)
    |> (·.size = 2)
  then
    some n
  else
    none

def find_smudgedₕ : Nat := cuts r.height |>.map (smudgedₕ r ·) |> sum
def find_smudgedᵥ : Nat := cuts r.width |>.map (smudgedᵥ r ·) |> sum
def evaluate : Nat := find_smudgedₕ r + find_smudgedᵥ r

def solve (pls : Array (Rect Bool)) : Nat := pls.map evaluate |> sum

end Part2

#guard (some #[3, 5]).map (·.shrink 1) == some #[3]

public def solve := AocProblem.config 2023 13 parser.parse Part1.solve Part2.solve

end Y2023.Day13
