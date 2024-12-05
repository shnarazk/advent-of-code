import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2024.Day04

open Accumulation CiCL
abbrev HashMap := Std.HashMap

def asNat : Bool -> Nat
  | false => 0
  | true => 1

structure Input where
  plane : HashMap (Int × Int) Char
deriving Repr

instance : ToString Input where toString self := s!"{self.plane.toList}"

def Input.xmas_n (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1 - 1, p.2) == some 'M'
      && self.plane.get? (p.1 - 2, p.2) == some 'A'
      && self.plane.get? (p.1 - 3, p.2) == some 'S'
    |> asNat

--
def Input.xmas_s (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1 + 1, p.2) == some 'M'
      && self.plane.get? (p.1 + 2, p.2) == some 'A'
      && self.plane.get? (p.1 + 3, p.2) == some 'S'
    |> asNat

--
def Input.xmas_e (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1, p.2 + 1) == some 'M'
      && self.plane.get? (p.1, p.2 + 2) == some 'A'
      && self.plane.get? (p.1, p.2 + 3) == some 'S'
    |> asNat

--
def Input.xmas_w (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1, p.2 - 1) == some 'M'
      && self.plane.get? (p.1, p.2 - 2) == some 'A'
      && self.plane.get? (p.1, p.2 - 3) == some 'S'
    |> asNat

--
def Input.xmas_ne (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1 - 1, p.2 + 1) == some 'M'
      && self.plane.get? (p.1 - 2, p.2 + 2) == some 'A'
      && self.plane.get? (p.1 - 3, p.2 + 3) == some 'S'
    |> asNat

--
def Input.xmas_es (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1 + 1, p.2 + 1) == some 'M'
      && self.plane.get? (p.1 + 2, p.2 + 2) == some 'A'
      && self.plane.get? (p.1 + 3, p.2 + 3) == some 'S'
    |> asNat

--
def Input.xmas_sw (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1 + 1, p.2 - 1) == some 'M'
      && self.plane.get? (p.1 + 2, p.2 - 2) == some 'A'
      && self.plane.get? (p.1 + 3, p.2 - 3) == some 'S'
    |> asNat

--
def Input.xmas_wn (self : Input) (p : Int × Int) : Nat :=
  self.plane.get? p == some 'X'
      && self.plane.get? (p.1 - 1, p.2 - 1) == some 'M'
      && self.plane.get? (p.1 - 2, p.2 - 2) == some 'A'
      && self.plane.get? (p.1 - 3, p.2 - 3) == some 'S'
    |> asNat

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_line : Parser (Array Char) := do
  let as ← alphabets
  return as.toList.toArray
-- #eval AoCParser.parse parse_line "eocb\n"

def parse_lines := sepBy1 parse_line eol
-- #eval AoCParser.parse parse_lines "eocb\nABC\n"

def parse : String → Option Input := AoCParser.parse parser
  where parser := do
    let v ← parse_lines
    let h := v.toList.enum.map (fun (i, l) ↦ l.toList.enum.map (fun (x : Nat × Char) ↦ (((i : Int), (x.1 : Int)), x.2)))
      |>.flatten
    return Input.mk (h.foldl (fun h (p, v) ↦ h.insert p v) Std.HashMap.empty)
-- #eval parse "ABC\nXYZ"

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.plane.toList.map
      (fun (p, _) ↦ input.xmas_n p + input.xmas_s p + input.xmas_e p + input.xmas_w p
        + input.xmas_ne p + input.xmas_es p + input.xmas_sw p + input.xmas_wn p)
    |> sum

end Part1

namespace Part2

def solve (input : Input) : Nat := input.plane.toList.length

end Part2

def solve := AocProblem.config 2024 04 parser.parse Part1.solve Part2.solve

end Y2024.Day04
