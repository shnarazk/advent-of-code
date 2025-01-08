import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2024.Day09

open Accumulation CiCL

structure Input where
  line : Array (Option Nat)
deriving BEq, Hashable, Repr

instance : ToString Input where
  toString s :=
    let v := s.line
      |>.map (fun o ↦ match o with | none => "." | some d => s!"{d}")
      |>.toList
      |> (String.join ·)
    s!"{s.line.size}: {v}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← many1 digit
      let disc := v.map (fun (c : Char) ↦ c.toNat - '0'.toNat)
       |>.enum
       |>.flatMap
            (fun (i, l) ↦ Array.mkArray l (if i % 2 == 0 then some ((i + 1) / 2) else none))
      return Input.mk disc

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 09
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day09
