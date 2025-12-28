module

-- public import Std.Data.Iterators.Combinators.Zip
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

namespace Y2025.Day09

open Std
open Accumulation Dim2

/-- return the distance between a and b -/
def dist (a b : Int) : Nat := (if a ≤ b then b - a else a - b).toNat

/-- return one plus the distance between a and b -/
def dist₁ (a b : Int) : Nat := (1 + if a ≤ b then b - a else a - b).toNat

structure Input where
  line : Array Idx₂
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line := (fun (a b : Nat) ↦ (↑(a, b) : Idx₂)) <$> number <* pchar ',' <*> number
def parse_input := separated parse_line eol

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> parse_input

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.line.iter
    |>.enumerate
    |>.map (fun (i, p) ↦
      input.line.iterFromIdx (i + 1)
        |>.map (fun (q : Idx₂) ↦ (dist₁ p.val.1 q.val.1) * (dist₁ p.val.2 q.val.2))
        |>.fold max 0)
    |>.fold max 0

end Part1

namespace Part2

def solve (input : Input) : Nat := Id.run do
  let ys := input.line.iter |>.map (·.val.fst) |>.toList |> HashSet.ofList |>.toArray |>.push 0 |>.qsort
  let encodeY := ys.iter.enumerate.map (fun (i, d) ↦ (d, i)) |>.toList |> HashMap.ofList
  let xs := input.line.iter |>.map (·.val.snd) |>.toList |> HashSet.ofList |>.toArray |>.push 0 |>.qsort
  let encodeX := xs.iter.enumerate.map (fun (i, d) ↦ (d, i)) |>.toList |> HashMap.ofList
  let mut sliceY : HashMap Nat (Array Nat) := HashMap.emptyWithCapacity 100
  let mut sliceX : HashMap Nat (Array Nat) := HashMap.emptyWithCapacity 100
  for p in input.line.iter do
    sliceY := sliceY.alter p.val.fst.toNat (fun o ↦ o)
    sliceX := sliceX.alter p.val.fst.toNat (fun o ↦ o)
  sliceY := sliceY.iter |>.map (fun (k, v) ↦ (k, v.qsort)) |>.toList |> HashMap.ofList
  sliceX := sliceX.iter |>.map (fun (k, v) ↦ (k, v.qsort)) |>.toList |> HashMap.ofList
  let gridSize := ys.size + 2
  let mut grid : Rect Nat := Rect.ofDim2 gridSize gridSize 3
  for (y, xs) in sliceY.iter do
    grid := grid.set (encodeY.get! y, encodeX.get! xs[0]!) 1 
    grid := grid.set (encodeY.get! y, encodeX.get! xs[1]!) 1 
    for x in (encodeX.get! xs[0]! + 1) ... (encodeX.get! xs[1]!) do grid := grid.set (encodeY.get! y, x) 2 
  for (x, ys) in sliceX.iter do
    for y in (encodeX.get! ys[0]! + 1) ... (encodeX.get! ys[1]!) do grid := grid.set (y, encodeY.get! x) 2 
  -- categorize the unvisited cells
  let mut toVisit : HashSet Idx₂ := HashSet.emptyWithCapacity 100
  toVisit := toVisit.insert (default : Idx₂)
  while !toVisit.isEmpty do
    break
  0

-- #eval toIdx₂ ((0, 8) : Vec₂) --.toIdx₂

end Part2

public def solve := AocProblem.config 2025 09 parser.parse Part1.solve Part2.solve

end Y2025.Day09
