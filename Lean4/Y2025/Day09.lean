module

public import Itertools
public import WinnowParsers
public import «AoC».Basic
public import «AoC».Vec

namespace Y2025.Day09

open Std
open Dim2

/-- return the distance between a and b -/
@[inline]
def dist (a b : Int) : Nat := (a - b).natAbs

/-- return one plus the distance between a and b -/
@[inline]
def dist₁ (a b : Int) : Nat := (a - b).natAbs + 1

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line := (fun (a b : Nat) ↦ (↑(b, a) : Idx₂)) <$> number <* pchar ',' <*> number

def parse : String → Option (Array Idx₂) := AoCParser.parse (separated parse_line eol)

end parser

def solve₁ (line : Array Idx₂) : Nat :=
  line.iter
    |>.enumerate
    |>.map (fun (i, p) ↦
      line.iterFromIdx (i + 1)
        |>.map (fun (q : Idx₂) ↦ (dist₁ p.1 q.1) * (dist₁ p.2 q.2))
        |>.fold max 0)
    |>.fold max 0

/--
  Use the following code for grid catrgorization
  - 0 : uncovered
  - 1 : corner
  - 2 : filled
  - 3 : unvisited -/
def solve₂ (line : Array Idx₂) : Nat := Id.run do
  let ys := line.iter |>.map (·.fst) |>.toList |> HashSet.ofList |>.toArray |>.push 0 |>.qsort
  let encodeY := ys.iter.enumerate.map (fun (i, d) ↦ (d, i)) |>.toList |> HashMap.ofList
  if encodeY.size == 0 then return 0
  let xs := line.iter |>.map (·.snd) |>.toList |> HashSet.ofList |>.toArray |>.push 0 |>.qsort
  let encodeX := xs.iter.enumerate.map (fun (i, d) ↦ (d, i)) |>.toList |> HashMap.ofList
  if encodeX.size == 0 then return 0
  let mut sliceY : HashMap Nat (Array Nat) := HashMap.emptyWithCapacity 100
  let mut sliceX : HashMap Nat (Array Nat) := HashMap.emptyWithCapacity 100
  for p in line.iter do
    sliceY := sliceY.alter p.fst (fun o ↦ o.mapOr (·.push p.snd) #[p.snd])
    sliceX := sliceX.alter p.snd (fun o ↦ o.mapOr (·.push p.fst) #[p.fst])
  sliceY := sliceY.iter |>.map (fun (k, v) ↦ (k, v.qsort)) |>.toList |> HashMap.ofList
  if sliceY.size == 0 then return 0
  sliceX := sliceX.iter |>.map (fun (k, v) ↦ (k, v.qsort)) |>.toList |> HashMap.ofList
  if sliceX.size == 0 then return 0
  let mut gridSize := ys.size + 1
  let mut grid : Rect Nat := Rect.ofDim2 gridSize gridSize 3
  for (y, xs) in sliceY.iter do
    grid := grid.set (encodeY.get! y, encodeX.get! xs[0]!) 1
    grid := grid.set (encodeY.get! y, encodeX.get! xs[1]!) 1
    for x in (encodeX.get! xs[0]! + 1) ... (encodeX.get! xs[1]!) do
      grid := grid.set (encodeY.get! y, x) 2
  for (x, ys) in sliceX.iter do
    for y in (encodeY.get! ys[0]! + 1) ... (encodeY.get! ys[1]!) do
      grid := grid.set (y, encodeX.get! x) 2
  -- categorize the unvisited cells
  let mut toVisit : Array Idx₂ := #[(default : Idx₂)]
  while !toVisit.isEmpty do
    let mut next : HashSet Idx₂ := HashSet.emptyWithCapacity 100
    for pos in toVisit.iter do
      let some state := grid[pos]? | continue
      if state != 3 then continue
      grid := grid.set pos 0
      for diff in Dir.eightNeighbors.iter do
        let some q := (↑ (pos + diff) : Option Idx₂) | continue
        let some state := grid[q]? | continue
        if state == 3 then next := next.insert q
    toVisit := next.toArray
  -- re-mark all unvisited as uncoverd
  grid := grid.map (fun k ↦ if k == 3 then 2 else k)
  -- search the maximum
  let mut area := 0
  for y' in 1...gridSize do
    for x' in 1...gridSize do
      if grid[(y', x')]? != some 1 then continue
      let mut min_x := 1
      for y in y' ... gridSize do
        for x_rev in min_x ...= x' do
          let x := x' + min_x - x_rev
          if grid[(y, x)]? == some 0 then min_x := x + 1 ; break
          if grid[(y, x)]? == some 1 then
            area := max area <| (dist₁ ys[y']! ys[y]!) * (dist₁ xs[x']! xs[x]!)
      let mut max_x := gridSize
      for y in y' ... gridSize do
        for x in x' ... max_x do
          if grid[(y, x)]? == some 0 then max_x := x ; break
          if grid[(y, x)]? == some 1 then
            area := max area <| (dist₁ ys[y']! ys[y]!) * (dist₁ xs[x']! xs[x]!)
      continue
  area

public def solve := AocProblem.config 2025 09 parser.parse solve₁ solve₂

end Y2025.Day09
