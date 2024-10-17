import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect

namespace TwoDimensionalVector.Rect

def mirrored_horizontally (frame : Rect Bool) (p : Dim2) (h : Nat) : Option Dim2 :=
  if p.y < h then
    let y' := h + h - p.y + 1
    if y' < frame.shape.y then some { p with y := y' } else none
  else
    let y' := p.y - h
    if h < y' then none else some { p with y := h - y' - 1 }

def r99 := Rect.ofDim2 (Dim2.mk 9 9) (by simp [NonNegDim]) false
#eval r99.mirrored_horizontally (Dim2.mk 1 5) 2

-- #eval mirrored_horizontally r99 (Dim2.mk 4 5) 4

def mirrored_vertically (frame : Rect Bool) (p : Dim2) (v : Nat) : Option Dim2 :=
  if p.x < v then
    let x' := v + v - p.x + 1
    if x' < frame.shape.x then some { p with x := x' } else none
  else
    let x' := p.x - v
    if v < x' then none else some { p with x := v - x' - 1 }

#eval r99.mirrored_horizontally (Dim2.mk 4 5) 4

end TwoDimensionalVector.Rect

namespace Y2023.Day13

open Std Accumulation CoP CiCL
open TwoDimensionalVector

variable (r : Rect Bool)

def cut_horizontally (n : Nat) : Option Nat :=
  if r.shape.toList.all (fun p ↦
    if let some q := r.mirrored_horizontally p n then
      r.get p = r.get q
    else
      false) then
    some n
  else
    none

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def maze_line := do
  let v ← many1 ((pchar '.').orElse fun _ ↦ pchar '#') <* eol
  return v.map (· == '#')

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Bool)) :=
  AoCParser.parse parser
  where
    parser := sepBy1 maze eol

end parser

namespace Part1

def solve (pls : Array (Rect Bool)) : Nat :=
  pls.map evaluate |> sum
  where
    pick_axis (n : Int) : List Nat := List.range n.toNat |>.drop 1 |>.dropLast
    valid_h_cut (m : Rect Bool) (h : Nat) : Option Nat := some 0
    evaluate (m : Rect Bool) : Nat :=
      dbgTrace s!"{pick_axis m.shape.y}" m.area
     -- List.range p.shape.y.toNat ** List.range p.shape.y.toNat
     --  |>.map

end Part1

namespace Part2

def solve (_ : Array (Rect Bool)) : Nat := 0

end Part2

#eval (some #[3, 5]).map (·.shrink 1)
def solve := AocProblem.config 2023 13
  ((·.map ((⎊toString‿dbgTrace‿K) ∘ (·.shrink 1))) ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day13
