import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Vec
import Init.Data.SInt.Basic

namespace Y2024.Day08

open Std Accumulation CiCL Dim2

-- syntax:50 term:51 " <₀ " term:50 : term
-- macro_rules | `($a <₀ $b) => `(Vec\_2.geZeroAndLt $b $a)

structure Input where
  anntena : List (Char × Vec₂)
  size: Vec₂
deriving BEq

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
        (fun (i, row) ↦ row.enum.toList.map (fun (j, c) ↦ (c, (i, j))))
        |>.flatten
        |>.filter (fun (c, _) ↦ c ≠ '.')
      return Input.mk a (v.size, v[0]!.size)

end parser

namespace Part1

partial def inbound_antinodes' (size a offset : Vec₂) : List Vec₂ :=
  let next := a + offset
  if next <₀ size then [next] else []

def inbound_antinodes (size : Vec₂) (a b : Char × Vec₂) : List Vec₂ :=
  if a.1 == b.1
    then inbound_antinodes' size a.2 (a.2 - b.2) ++ inbound_antinodes' size b.2 (b.2 - a.2)
    else []

def solve (input : Input) : Nat :=
  input.anntena.enumerate.map
    (fun (i, a1) ↦ input.anntena.drop (i + 1) |>.flatMap (fun a2 ↦ inbound_antinodes input.size a1 a2))
    |>.flatten
    |> HashSet.ofList
    |>.size

end Part1

namespace Part2

partial def inbound_antinodes' (size a offset : Vec₂) : List Vec₂ :=
  let next := a + offset
  if next <₀ size then [next] ++ inbound_antinodes' size next offset else []

def inbound_antinodes (size : Vec₂) (a b : Char × Vec₂) : List Vec₂ :=
  if a.1 == b.1
    then [a.2, b.2] ++ inbound_antinodes' size a.2 (a.2 - b.2) ++ inbound_antinodes' size b.2 (b.2 - a.2)
    else []

def solve (input : Input) : Nat :=
    input.anntena.enumerate.map
    (fun (i, a1) ↦ input.anntena.drop (i + 1) |>.flatMap (fun a2 ↦ inbound_antinodes input.size a1 a2))
    |>.flatten
    |> HashSet.ofList
    |>.size

end Part2

def solve := AocProblem.config 2024 08 parser.parse Part1.solve Part2.solve

end Y2024.Day08
