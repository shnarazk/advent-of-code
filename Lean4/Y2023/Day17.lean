import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import «AoC».Rect64

namespace Y2023.Day17

open Accumulation CiCL
open TwoDimensionalVector64

structure Input where
deriving BEq, Repr

instance : ToString Input where toString _ := s!""

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def line : Parser (Array Nat) := do
  let l ← many1 digit <* eol
  return l.map (fun (c : Char) ↦ (c.val - '0'.val).toNat)

def matrix := many1 line
def parse : String → Option (Rect Nat) := AoCParser.parse parse
  where
    parse := pure ∘ Rect.of2DMatrix =<< matrix

end parser

abbrev State := Dim2 × Nat

def next_positions (r : Rect Nat) (pos : Dim2) (turn : Nat) : List State :=
  let h := r.height
  let w := r.width
  let go_n := (0 < pos.fst     : Bool).map (K ((pos.fst - 1, pos.snd), turn + 1))
  let go_s := (pos.fst < h - 1 : Bool).map (K ((pos.fst + 1, pos.snd), turn + 1))
  let go_w := (0 < pos.snd     : Bool).map (K ((pos.fst, pos.snd - 1), turn + 1))
  let go_e := (pos.snd < w - 1 : Bool).map (K ((pos.fst, pos.snd + 1), turn + 1))
  []

namespace Part1
variable (visited : Std.HashSet State)
variable (to_visit : List State)

partial def find (r : Rect Nat) (vt : Std.HashSet State × List State) : Nat :=
  let (visited, to_visit) := vt
  match to_visit with
  | [] => r.get (r.height - 1) r.width 0
  | (pos, _dist) :: to_visit' =>
    let _w := r.get pos.fst pos.snd 0
    find r (visited, to_visit')

def solve (r : Rect Nat) : Nat := 0

end Part1

namespace Part2

def solve (_ : Rect Nat) : Nat := 0

end Part2

def solve := AocProblem.config 2023 17 parser.parse Part1.solve Part2.solve

end Y2023.Day17
