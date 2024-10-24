import Std
import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2023.Day15

open Std Accumulation CiCL

abbrev Input := Array (Array Char)

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def segments := sepBy1
  (many1 (satisfy (!",\n".contains ·)))
  (satisfy (",\n".contains ·))

def parse : String → Option Input := AoCParser.parse segments

-- #eval parse "abc,de=,cko"

end parser

namespace Part1

def solve (data : Input) : Nat :=
  data.map (fun chars ↦ chars.foldl
    (fun current c ↦ current + c.val.toNat |> (· * 17) |> (· % 256)) 0)
  |> sum

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2023 15 parser.parse Part1.solve Part2.solve

end Y2023.Day15
