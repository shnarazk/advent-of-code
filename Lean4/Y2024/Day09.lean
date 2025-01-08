import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2024.Day09

open Accumulation CiCL

structure Input where
  line : Array Nat
deriving BEq, Hashable, Repr

instance : ToString (Array (Option Nat)) where
  toString s :=
    let v := s
      |>.map (fun o ↦ match o with | none => "." | some d => s!"{d}")
      |>.toList
      |> (String.join ·)
    s!"{s.size}: {v}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
      let v ← many1 digit
      return Input.mk (v.map (fun (c : Char) ↦ c.toNat - '0'.toNat))

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
  let disc := input.line
    |>.enum
    |>.flatMap
      (fun (i, l) ↦ Array.mkArray l (if i % 2 == 0 then some ((i + 1) / 2) else none))
  swap disc 0 (disc.size - 1)
   |>.enum
   |>.map (fun (i, v) ↦ i * v.unwrapOr 0)
   |> sum

end Part1

namespace Part2

partial def seek (start len target : Nat) (free_start free_len : Array Nat)
    : (Nat × Nat) × Array Nat × Array Nat :=
  if free_start.getD target start ≥ start then ((start, len), free_start, free_len)
  else if len > free_len.get! target then seek start len (target + 1) free_start free_len
    else
      let start'      := free_start.get! target
      let free_start' := free_start.modify target (· + len)
      let free_len'   := free_len.modify target (· - len)
      ((start', len), free_start', free_len')

partial def swap (files : List (Nat × Nat)) (free_start free_len : Array Nat) : List (Nat × Nat) :=
  match files with
    | [] => []
    | (start, len) :: remain =>
      let (result, free_start', free_len') := seek start len 0 free_start free_len
      result :: swap remain free_start' free_len'


def solve (input : Input) : Nat :=
  let file_len := input.line.enum.filter (fun (i, _) ↦ i % 2 == 0) |>.map (·.2)
  let free_len := input.line.enum.filter (fun (i, _) ↦ i % 2 == 1 ) |>.map (·.2)
  let file_start := input.line.enum.foldl
      (fun (list, i) (id, len) ↦ (if id % 2 == 0 then list ++ [i] else list, i + len))
      ([], 0)
    |>.1
  let free_start := input.line.enum.foldl
      (fun (list, i) (id, len) ↦ (if id % 2 == 1 then list ++ [i] else list, i + len))
      ([], 0)
    |>.1
    |>.toArray
  let target_files := file_start.zip file_len.toList |>.reverse
  swap target_files free_start free_len
   |>.reverse
   |>.enum
   |>.map (fun (id, (start, len)) ↦ List.range len |>.map (fun i ↦ (start + i) * id) |> sum)
   |> sum

end Part2

def solve := AocProblem.config 2024 09 parser.parse Part1.solve Part2.solve

end Y2024.Day09
