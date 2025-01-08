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

partial def next (disc : Array (Option Nat)) ( limit_left limit_right i : Nat) (increase : Bool) : Nat :=
  if disc.getD i none == none then i
    else
      if not increase && i == limit_left then i
        else if increase && i == limit_right then i
          else
            next disc limit_left limit_right (if increase then i + 1 else i - 1) increase

partial def swap (disc : Array (Option Nat)) (left right : Nat) : Array (Option Nat) :=
  if left < right then disc
    else
      let l := next disc 0 (disc.size - 1) left true
      let r := next disc 0 (disc.size - 1) right false
      if r <= l then disc else swap (disc.swapIfInBounds l r) (l + 1) (r - 1)

def solve (input : Input) : Nat :=
  let moved := swap input.line 0 (input.line.size - 1)
  moved.size

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 09
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day09
