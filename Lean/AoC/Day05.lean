import Std
import «AoC».Basic
import «AoC».Parser
import Lean.Data.Parsec

namespace Day05

structure ClosedSpan where
  new ::
  _beg : Nat
  _end : Nat
deriving Repr

instance : ToString ClosedSpan where
  toString s := s!"[{s._beg},{s._end}]"

structure Range where
  dest   : Nat
  source : Nat
  span   : Nat
deriving Repr

instance : ToString Range where
  toString r := s!"({r.dest},{r.source},{r.span})"

namespace parser
open Lean Parsec AoCParser

def pseeds := pstring "seeds: " *> sepBy1 number whitespaces <* eol <* eol

def plabel := do
  let _ ← alphabets <* pstring "-to-"
  let _ ← alphabets <* pstring " map:\n"
  return ()

-- #eval Parsec.run plabel "water-to-light map:\n"

def range := do
  let d ← number <* separator ' '
  let s ← number <* separator ' '
  let r ← number <* separator₀ ' '
  return ({ dest := d, source := s, span := r } : Range)

def pmap := sepBy1 range eol

-- #eval Parsec.run pmap "88 18 7"
-- #eval Parsec.run pmap "88 18 7\n18 25 70"

-- def parser : Parsec Range := (plabel *> range)
def parser : Parsec ((Array Nat) × (Array (Array Range))) := do
  let ss ← pseeds
  let ms ← sepBy1 (plabel *> pmap) (pstring "\n\n")
  return (ss, ms)

-- #eval Parsec.run parser "seeds: 2 5\n\na-to-b map:\n88 18 7"

end parser

def transpose₀ (pos : Nat) (rs : List Range) : Nat :=
  match rs with
  | [] => pos
  | List.cons range rs' =>
      if range.source ≤ pos && pos < range.source + range.span
      then range.dest + pos - range.source
      else transpose₀ pos rs'

def transpose (seeds : Array Nat) (rs : Array Range) :=
  seeds.map (transpose₀ · rs.toList)

def Part1.solve (data : String) : IO (Array Nat × Array (Array Range)) := do
  if let some (seeds, maps) := AoCParser.parse parser.parser data then
    IO.println s!"  part1: {maps.foldl transpose seeds |>.minD 0}"
    return (seeds, maps)
  return panic "parse error"

def pairs (l : List α) : List (α × α) :=
  match l with
  | [] => []
  | a :: b :: c => (a, b) :: pairs c
  | _ :: _ => panic! "impossible"

#eval pairs <| List.range 6

/--
return `Option converted-span` and `List non-converted-span`
-/
def transpose_span (span : ClosedSpan) (range : Range)
    : (Option ClosedSpan) × (List ClosedSpan) :=
  let b : Nat := Nat.max span._beg range.source
  let e : Nat := Nat.min span._end (range.source + range.span - 1)
  if (b ≤ e : Bool)
  then
    (some (ClosedSpan.new (range.dest + b - range.source) (range.dest + e - range.source)),
        match (span._beg < b : Bool), (e < span._end : Bool) with
        | false, false => []
        | false, true  => [ClosedSpan.new (e + 1) span._end]
        | true,  false => [ClosedSpan.new span._beg (b - 1)]
        | true,  true  => [ClosedSpan.new span._beg (b - 1), ClosedSpan.new (e + 1) span._end])
  else (none, [span])

def tp2 (spans : List ClosedSpan) (stages : Array (Array Range)) : List ClosedSpan :=
  Array.foldl (fun spans' stage =>
      stage.foldl (fun (not_yet, done) rule =>
          not_yet.foldl (fun (accum : List ClosedSpan × List ClosedSpan) (span : ClosedSpan) =>
              match transpose_span span rule with
              | (some s', rest) => (accum.fst ++ rest, accum.snd ++ [s'])
              | (none   , rest) => (accum.fst ++ rest, accum.snd))
            ([], [])
          |> (fun (r, d) => (r, done ++ d)))
        (spans', ([] : List ClosedSpan))
      |>( fun (r, d) => r ++ d))
    spans
    (stages : Array (Array Range))

def Part2.solve (data : Array Nat × Array (Array Range)) : IO Unit := do
  let (d, rule) := data
  let spans := pairs d.toList |>.map (fun (b, e) => ClosedSpan.new b (b + e))
  let spans' : List ClosedSpan := tp2 spans rule
  IO.println s!"  part2: {spans'.map (·._beg) |>.minimum? |>.getD 0}"

end Day05

def day05 (ext : Option String) : IO Unit := do
  dataOf 2023 5 ext >>= Day05.Part1.solve >>= Day05.Part2.solve
