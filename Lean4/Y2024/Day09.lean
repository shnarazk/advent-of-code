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

partial def nextEmpty (disc : Array (Option Nat)) (limit i : Nat) : Nat :=
  if disc.getD i none == none then i
    else if i == limit then limit
    else nextEmpty disc limit (i + 1)

partial def nextUsed (disc : Array (Option Nat)) (limit i : Nat) : Nat :=
    if let some _ := disc.getD i (some 0) then i
      else if i == limit then limit
      else nextUsed disc limit (i - 1)

partial def swap (disc : Array (Option Nat)) (left right : Nat) : Array (Option Nat) :=
  if left ≥ right then disc
    else
      let l := nextEmpty disc (disc.size - 1) left
      let r := nextUsed disc 0 right
      if r <= l then disc else swap (disc.swapIfInBounds l r) (l + 1) (r - 1)

def solve (input : Input) : Nat :=
  swap input.line 0 (input.line.size - 1)
   |>.enum
   |>.map (fun (i, v) ↦ i * v.unwrapOr 0)
   |> sum

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 09 parser.parse Part1.solve Part2.solve

end Y2024.Day09
