import Std.Internal.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2023.Day11
open CoP
open Std

structure Data where
  new   ::
  size  : Nat × Nat
  array : Array Bool
deriving Repr

namespace Data

-- #eval #[false, false, true, false].size
-- #eval Data.new (2, 2) #[false, false, true, false]

instance : ToString Data where
  toString s := s!"({toString s.size})[{toString s.array}]"

end Data

namespace parser
open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def pcell := (pchar '.' *> return false) <|> (pchar '#' *> return true)
def parse := AoCParser.parse $ sepBy1 (many1 pcell) eol

end parser

def dist (a b : Nat) : Nat := Nat.max (a - b) (b - a)

def sum_of_dist : List (Nat × Nat) → Nat
  |     [] => 0
  |    [_] => 0
  | a :: b => sum_of_dist b + b.foldl (fun sum e => sum + join Nat.add (both2 dist e a)) 0

def expand (m : List Nat) (r : Nat) (s : Nat) : List Nat :=
  List.range r
    |>.foldl (fun (base, result) i =>
       (if m.all (· != i) then base + s else base, result ++ [i + base]))
      (0, ([] : List Nat))
    |>.snd

def Part1.solve (d: Array (Array Bool)) : Nat :=
  let m := d.map (·.foldl (fun (j, l) b => (j + 1, if b then l ++ [j] else l)) (0, []))
    |>.map (·.snd)
    |>.foldl (fun (i, l) e => (i + 1, l ++ e.map ((i, ·)))) (0, ([] : List (Nat × Nat)))
    |>.snd
  let range := m.foldl (fun m e => (max m.fst e.fst, max m.snd e.snd)) (0, 0)
    |> (fun p => (p.fst + 1, p.snd + 1))
  -- build transformation map
  let trans_y : List Nat := expand (m.map (·.fst)) range.fst 1
  let trans_x : List Nat := expand (m.map (·.snd)) range.snd 1
  sum_of_dist $ m.map (fun (y, x) => (trans_y[y]!, trans_x[x]!))

def Part2.solve (d: Array (Array Bool)) : Nat :=
  let m := d.map (·.foldl (fun (j, l) b => (j + 1, if b then l ++ [j] else l)) (0, []))
    |>.map (·.snd)
    |>.foldl (fun (i, l) e => (i + 1, l ++ e.map ((i, ·)))) (0, ([] : List (Nat × Nat)))
    |>.snd
  let range := m.foldl (fun m e => (max m.fst e.fst, max m.snd e.snd)) (0, 0)
    |> (fun p => (p.fst + 1, p.snd + 1))
  -- build transformation map
  let scaling := 1000000 - 1
  let trans_y : List Nat := expand (m.map (·.fst)) range.fst scaling
  let trans_x : List Nat := expand (m.map (·.snd)) range.snd scaling
  sum_of_dist $ m.map (fun (y, x) => (trans_y[y]!, trans_x[x]!))

def solve := AocProblem.new 2023 11 |>.build parser.parse Part1.solve Part2.solve

end Y2023.Day11
