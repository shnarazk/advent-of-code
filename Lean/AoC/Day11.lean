import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Day11
open CoP
open Std

structure Data where
  new   ::
  size  : Nat × Nat
  array : Array Bool
deriving Repr

namespace Data

#eval #[false, false, true, false].size
#eval Data.new (2, 2) #[false, false, true, false]

instance : ToString Data where
  toString s := s!"({toString s.size})[{toString s.array}]"

end Data

namespace parser
open Lean.Parsec AoCParser

def pcell := (pchar '.' *> return false) <|> (pchar '#' *> return true)
def parser := do
  sepBy1 (many1 pcell) eol
  -- return Array.join a
  -- return Data.new (a.size, a[0]!.size) (Array.join a)

end parser

def dist (a b : Nat) : Nat := Nat.max (a - b) (b - a)

def sum_of_dist : List (Nat × Nat) → Nat
  | [] => 0
  | _ :: [] => 0
  | a :: b =>
    let dists := b.foldl (fun sum e => sum + join Nat.add (both2 dist e a)) 0
    dists + sum_of_dist b

#eval Nat.sub 3 1

def Part1.solve (data : String) : IO Unit := do
  if let some d := AoCParser.parse parser.parser data then
    let m := d.map (·.foldl (fun (j, l) b => (j + 1, if b then l ++ [j] else l)) (0, []))
      |>.map (·.snd)
      |>.foldl (fun (i, l) e => (i + 1, l ++ e.map ((i, ·)))) (0, ([] : List (Nat × Nat)))
      |>.snd
    let range := m.foldl (fun m e => (max m.fst e.fst, max m.snd e.snd)) (0, 0)
      |> (fun p => (p.fst + 1, p.snd + 1))
    -- build transformation map
    let trans_y := List.range range.fst
      |>.foldl (fun (base, result) i =>
         (if m.all (·.fst != i) then base + 1 else base, result ++ [i + base]))
        (0, ([] : List Nat))
      |>.snd
    let trans_x := List.range range.snd
      |>.foldl (fun (base, result) i =>
         (if m.all (·.snd != i) then base + 1 else base, result ++ [i + base]))
        (0, ([] : List Nat))
      |>.snd
    -- scale up
    let m' := m.map (fun p => (trans_y[p.fst]!, trans_x[p.snd]!))
    IO.println s!"  part1: {sum_of_dist m'}"

def Part2.solve (data : String) : IO Unit := do
  if let some d := AoCParser.parse parser.parser data then
    let m := d.map (·.foldl (fun (j, l) b => (j + 1, if b then l ++ [j] else l)) (0, []))
      |>.map (·.snd)
      |>.foldl (fun (i, l) e => (i + 1, l ++ e.map ((i, ·)))) (0, ([] : List (Nat × Nat)))
      |>.snd
    let range := m.foldl (fun m e => (max m.fst e.fst, max m.snd e.snd)) (0, 0)
      |> (fun p => (p.fst + 1, p.snd + 1))
    -- build transformation map
    let scaling := 1000000 - 1
    let trans_y := List.range range.fst
      |>.foldl (fun (base, result) i =>
         (if m.all (·.fst != i) then base + scaling else base, result ++ [i + base]))
        (0, ([] : List Nat))
      |>.snd
    let trans_x := List.range range.snd
      |>.foldl (fun (base, result) i =>
         (if m.all (·.snd != i) then base + scaling else base, result ++ [i + base]))
        (0, ([] : List Nat))
      |>.snd
    -- scale up
    let m' := m.map (fun p => (trans_y[p.fst]!, trans_x[p.snd]!))
    IO.println s!"  part2: {sum_of_dist m'}"

end Day11

def day11 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 11 ext
  Day11.Part1.solve data
  Day11.Part2.solve data
