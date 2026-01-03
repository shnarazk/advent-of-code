module

public import Itertools
public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec3

namespace Y2025.Day08

open Dim3 Std

structure Input where
  boxes : Array Vec₃
  dists : Array (Nat × (Nat × Nat))
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
    parser : Parser Input := do
    let boxes ← separated parse_dim3 eol
    let mut dists : Array (Nat × (Nat × Nat)) := #[]
    for (i, b1) in boxes.iter.enumerate do
      for (j, b2) in boxes.iter.enumerate do
        if j ≤ i then continue
        let d := b1 - b2
        dists := dists.push (d.x.natAbs ^ 2 + d.y.natAbs ^ 2 + d.z.natAbs ^ 2, i, j)
    dists := dists.heapSort (·.fst < ·.fst)
    pure <| Input.mk boxes dists

end parser

namespace Part1

def solve (input : Input) : Nat := Id.run do
  let num_boxes := input.boxes.size
  let mut group : Batteries.UnionFind := Batteries.UnionFind.mkEmpty num_boxes
  while group.size < num_boxes do group := group.push
  for (_, (i, j)) in input.dists.take 1000 do group := group.union! i j
  let mut groupSizes : HashMap Nat Nat := HashMap.emptyWithCapacity (num_boxes / 4)
  for i in 0 ... num_boxes do
    groupSizes := groupSizes.alter (group.root! i) (fun o ↦ o.mapOr (· + 1) 1 |> some)
  let mut v : Array Nat := groupSizes.values.toArray.heapSort (· > ·) |>.take 3
  v.foldl (· * ·) 1 |> pure

end Part1

namespace Part2

def solve (input : Input) : Nat := Id.run do
  let num_boxes := input.boxes.size
  let mut group : Batteries.UnionFind := Batteries.UnionFind.mkEmpty num_boxes
  while group.size < num_boxes do group := group.push
  for (_, (i, j)) in input.dists do
    group := group.union! i j
    let root := group.root! 0
    if (0...num_boxes).iter.all (group.root! · == root) then
      return (input.boxes[i]?.mapOr (·.x.toNat) 0) * (input.boxes[j]?.mapOr (·.x.toNat) 0)
  0

end Part2

public def solve := AocProblem.config 2025 08 parser.parse Part1.solve Part2.solve

end Y2025.Day08
