module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec3

namespace Y2025.Day08

open Accumulation Dim3 Std

structure Input where
  boxes : Array Vec₃
deriving BEq

instance : ToString Input where toString s := s!"{s.boxes}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_dim3 := do
  let x ← number <* pchar ','
  let y ← number <* pchar ','
  let z ← number
  pure <| Vec₃.mk z y x

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do Input.mk <$> separated parse_dim3 eol

end parser

namespace Part1

def solve (input : Input) : Nat := Id.run do
  let mut dists : Array (Nat × (Nat × Nat)) := #[]
  for (i, b1) in input.boxes.enum do
    for (j, b2) in input.boxes.enum.drop (i + 1) do
      let d := b1 - b2
      dists := dists.push (d.x.natAbs ^ 2 + d.y.natAbs ^ 2 + d.z.natAbs ^ 2, i, j)
  dists := dists.heapSort (·.fst < ·.fst)
  let mut groups : Array Nat := #[]
  let mut toGroup : HashMap Nat Nat := HashMap.emptyWithCapacity 1000
  let mut next_gid := 0
  for (_, (i, j)) in dists.take 1000 do
    match toGroup.get? i, toGroup.get? j with
    | none, none =>
      toGroup := toGroup.insert i next_gid
      toGroup := toGroup.insert j next_gid
      groups := groups.push 0
      next_gid := next_gid + 1
    | none, some gj => toGroup:= toGroup.insert i gj
    | some gi, none => toGroup:= toGroup.insert j gi
    | some g1', some g2' =>
      let mut g1 := g1'
      while groups[g1]! != 0 do g1 := groups[g1]!
      let mut g2 := g2'
      while groups[g2]! != 0 do g2 := groups[g2]!
      if g1 ≠ g2 then
        groups := groups.set! g1 next_gid
        groups := groups.set! g2 next_gid
        groups := groups.push 0
        next_gid := next_gid + 1
  let mut groupSizes : HashMap Nat Nat := HashMap.emptyWithCapacity (next_gid / 4)
  for (_, g') in toGroup do
    let mut g := g'
    while groups[g]! != 0 do g := groups[g]!
    groupSizes := groupSizes.alter g (fun o ↦ o.mapOr (· + 1) 1 |> some)
  let mut v : Array Nat := groupSizes.values.toArray.heapSort (· > ·) |>.take 3
  v.foldl (· * ·) 1 |> pure

end Part1

namespace Part2

def solve (input : Input) : Nat := Id.run do
  let mut dists : Array (Nat × (Nat × Nat)) := #[]
  for (i, b1) in input.boxes.enum do
    for (j, b2) in input.boxes.enum.drop (i + 1) do
      let d := b1 - b2
      dists := dists.push (d.x.natAbs ^ 2 + d.y.natAbs ^ 2 + d.z.natAbs ^ 2, i, j)
  dists := dists.heapSort (·.fst < ·.fst)
  let mut groups : Array Nat := #[]
  let mut toGroup : HashMap Nat Nat := HashMap.emptyWithCapacity 100
  let mut next_gid := 0
  let num_boxes := input.boxes.size
  let mut num_groups := 0
  for (_, (i, j)) in dists do
    assert! (i != j)
    match toGroup.get? i, toGroup.get? j with
    | none, none =>
      toGroup := toGroup.insert i next_gid
      toGroup := toGroup.insert j next_gid
      groups := groups.push 0
      next_gid := next_gid + 1
      num_groups := num_groups + 1
    | none, some gj => toGroup:= toGroup.insert i gj
    | some gi, none => toGroup:= toGroup.insert j gi
    | some g1', some g2' =>
      let mut g1 := g1'
      while groups[g1]! != 0 do g1 := groups[g1]!
      let mut g2 := g2'
      while groups[g2]! != 0 do g2 := groups[g2]!
      if g1 ≠ g2 then
        groups := groups.set! g1 next_gid
        groups := groups.set! g2 next_gid
        groups := groups.push 0
        next_gid := next_gid + 1
        num_groups := num_groups - 1
    if num_groups == 1 && toGroup.size == num_boxes then
      return (input.boxes[i]?.mapOr (·.x.toNat) 0) * (input.boxes[j]?.mapOr (·.x.toNat) 0)
  0

end Part2

public def solve := AocProblem.config 2025 08 parser.parse Part1.solve Part2.solve

end Y2025.Day08
