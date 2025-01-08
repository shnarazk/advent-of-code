import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64
import Init.Data.SInt.Basic

namespace Y2024.Day08

open Std Accumulation CiCL TwoDimensionalVector64

abbrev Vec2 := Int64 × Int64
instance : ToString Vec2 where toString v := s!"({v.1},{v.2})"
instance : Hashable Int64 where hash a := a.toUInt64
-- instance : Hashable Vec2 where hash a := hash (a.1)

instance : HAdd Vec2 Vec2 Vec2 where
  hAdd (a b : Vec2) : Vec2 := (a.1 + b.1, a.2 + b.2)

instance : HSub Vec2 Vec2 Vec2 where
  hSub (a b : Vec2) : Vec2 := (a.1 - b.1, a.2 - b.2)

def contains (size pos : Vec2) : Bool :=
  0 ≤ pos.1 && pos.1 < size.1 && 0 ≤ pos.2 && pos.2 < size.2

structure Input where
  anntena : List (Char × Vec2)
  size: Vec2
deriving BEq
-- #check ((4, 8) : Dim2)

instance : ToString Input where toString s := s!"({s.size}){s.anntena}"

namespace parser

open Std
open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseSymbol := do asciiLetter <|> digit <|> pchar '.'

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← sepBy1 (many1 parseSymbol) eol
      let a := v.enum.toList.map
        (fun (i, row) ↦ row.enum.toList.map (fun (j, c) ↦ (c, (i.toInt64, j.toInt64))))
        |>.flatten
        |>.filter (fun (c, _) ↦ c ≠ '.')
      return Input.mk a (v.size.toInt64, v[0]!.size.toInt64)

end parser

namespace Part1

partial def inbound_antinodes' (size a offset : Vec2) : List Vec2 :=
  let next := a + offset
  if contains size next then [next] else []

def inbound_antinodes (size : Vec2) (a b : Char × Vec2) : List Vec2 :=
  if a.1 == b.1
    then inbound_antinodes' size a.2 (a.2 - b.2) ++ inbound_antinodes' size b.2 (b.2 - a.2)
    else []

def solve (input : Input) : Nat :=
  input.anntena.enum.map
    (fun (i, a1) ↦ input.anntena.drop (i + 1) |>.flatMap (fun a2 ↦ inbound_antinodes input.size a1 a2))
    |>.flatten
    |> HashSet.ofList
    |>.size

end Part1

namespace Part2

partial def inbound_antinodes' (size a offset : Vec2) : List Vec2 :=
  let next := a + offset
  if contains size next then [next] ++ inbound_antinodes' size next offset else []

def inbound_antinodes (size : Vec2) (a b : Char × Vec2) : List Vec2 :=
  if a.1 == b.1
    then [a.2, b.2] ++ inbound_antinodes' size a.2 (a.2 - b.2) ++ inbound_antinodes' size b.2 (b.2 - a.2)
    else []

def solve (input : Input) : Nat :=
    input.anntena.enum.map
    (fun (i, a1) ↦ input.anntena.drop (i + 1) |>.flatMap (fun a2 ↦ inbound_antinodes input.size a1 a2))
    |>.flatten
    |> HashSet.ofList
    |>.size

end Part2

def solve := AocProblem.config 2024 08 parser.parse Part1.solve Part2.solve

end Y2024.Day08
