module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Rect64

def cuts (g : UInt64) : List Nat := List.range g.toNat |>.drop 1

namespace TwoDimensionalVector64.Dim2

end TwoDimensionalVector64.Dim2

namespace TwoDimensionalVector64.Rect

variable (r : Rect Bool)

def mirroredₕ (p : Dim2) (h' : Nat) : Option Dim2 :=
  let h : UInt64 := h'.toUInt64
  if p.1 < h then
    let y' : UInt64 := h + h - p.1 - 1
    if y' < r.height then some (y', p.2) else none
  else
    let y' := p.1 - h
    if h < y' + 1 then none else some (h - y' - 1, p.2)

-- def r99 := Rect.ofDim2 (Dim2.mk 5 6) (by simp [NonNegDim]) false
-- def p := Dim2.mk 1 5
-- #eval r99.mirroredₕ p 2
-- #eval if let some q := r99.mirroredₕ p 2 then r99.mirroredₕ q 2 else none
-- #eval mirroredₕ r99 (Dim2.mk 4 5) 2

/--
Return optinal Dim2 that locates on the mirrored position.
-/
def mirroredᵥ (p : Dim2) (v' : Nat) : Option Dim2 :=
  let v : UInt64 := v'.toUInt64
  if p.2 < v then
    let x' : UInt64 := (v + v) - p.2 - 1
    if x' < r.width then some (p.1, x') else none
  else
    let x' : UInt64 := p.2 - v
    if v < x' + 1 then none else some (p.1, v - x' - 1)

-- #eval r99.mirroredᵥ (Dim2.mk 4 5) 4

-- #eval r99.cutᵥ 1

end TwoDimensionalVector64.Rect

namespace Y2023.Day13

open Accumulation CoP CiCL
open TwoDimensionalVector64

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

variable (r : Rect Bool)

def cutₕ (r : Rect Bool) (n : Nat) : Option Nat :=
  -- 対応するものがなければ `true`
  if r.indices.all (fun p ↦ r.mirroredₕ p n |>.mapOr (r.get p false = r.get · false) true) then
    some (n * 100)
  else
    none

-- #eval r99.cutₕ 1
-- #eval r99.get (Dim2.mk 1 1) true = r99.get (Dim2.mk 1 2) true

def cutᵥ (r : Rect Bool) (n : Nat) : Option Nat :=
  if r.indices.all (fun p ↦ r.mirroredᵥ p n |>.mapOr (r.get p false = r.get · false) true) then
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
  if r.indices.map (fun p ↦ r.mirroredₕ p n |>.mapOr (r.get p false != r.get · false) false)
      |>.filter (·)
      |> (·.length = 2)
  then
    some (n * 100)
  else
    none

def smudgedᵥ (r : Rect Bool) (n : Nat) : Option Nat :=
  if r.indices.map (fun p ↦ r.mirroredᵥ p n |>.mapOr (r.get p false != r.get · false) false)
    |>.filter (·)
    |> (·.length = 2)
  then
    some n
  else
    none

def find_smudgedₕ : Nat := cuts r.height |>.map (smudgedₕ r ·) |> sum
def find_smudgedᵥ : Nat := cuts r.width |>.map (smudgedᵥ r ·) |> sum
def evaluate : Nat := find_smudgedₕ r + find_smudgedᵥ r

def solve (pls : Array (Rect Bool)) : Nat := pls.map evaluate |> sum

end Part2

-- #eval (some #[3, 5]).map (·.shrink 1)

public def solve := AocProblem.config 2023 13 parser.parse Part1.solve Part2.solve

end Y2023.Day13
