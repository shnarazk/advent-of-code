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

def parse_box : String → Option (String × Nat) := AoCParser.parse p
  where
    p := do
      let label ← alphabets <* pchar '='
      let val ← digits
      return (label, val)
-- #eval parse_box "ab=85"

def parse_ers : String → Option String := AoCParser.parse p
  where
    p := do
      let label ← alphabets <* pchar '-'
      return label
-- #eval parse_ers "ab-"

end parser

namespace Part1

def hasher (str : Array Char) : Nat :=
  str.foldl (fun acc c ↦ ((acc + c.val.toNat) * 17) % 256) 0

def solve (data : Input) : Nat := data.map hasher |> sum

end Part1

namespace Part2

def windows2 {α : Type} (l : List α) : List (α × α) :=
  match l with
  | [] => []
  | k :: v :: l' => (k, v) :: windows2 l'
  | e => dbgTrace s!"unreachable: {e.length}" (fun _ => [])
-- #eval windows2 "abcdefgh".toList

-- #eval String.mk #['a', 'c'].toList

/- We need `push-tail` operetion -/
abbrev AssocList := List (String × Nat)

def assoc_insert (al : AssocList) (tag : String) (val : Nat) : AssocList :=
  let (l, found) := al.foldr
    (fun (k, v) (l, found) ↦ if k == tag then ((k, val) :: l, true) else ((k, v) :: l, found))
    ([], false)
  if found then l else al ++ [(tag, val)]

def assoc_erase (al : AssocList) (tag : String) : AssocList :=
  al.foldr (fun (k, v) l ↦ if k == tag then l else (k, v) :: l) []

def solve (data : Input) : Nat :=
  data.foldl
      (fun boxes ac ↦
        let str : String := String.mk ac.toList
        if let some (tag, val) := parser.parse_box str then
          boxes.modify (Part1.hasher tag.toList.toArray) (assoc_insert · tag val)
        else if let some tag := parser.parse_ers str then
          boxes.modify (Part1.hasher tag.toList.toArray) (assoc_erase · tag)
        else dbgTrace ("unparsable: " ++ str) (fun _ ↦ boxes)
      )
      (Array.mkArray 256 [])
    |>.foldl
        (fun (acc, index) al ↦
          al.foldl
              (fun (acc, i) (_, val) ↦ (acc + index * i * val, i + 1))
              (acc, 1)
            |>(·.fst, index + 1))
        (0, 1)
    |>.fst

end Part2

def solve := AocProblem.config 2023 15 parser.parse Part1.solve Part2.solve

end Y2023.Day15
