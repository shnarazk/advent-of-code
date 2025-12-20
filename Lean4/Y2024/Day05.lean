module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2024.Day05

open Accumulation CiCL

structure Input where
  rules : Array (Nat × Nat)
  updates : Array (Array Nat)
deriving BEq, Repr

instance : ToString Input where toString self := s!"{self.rules.size}/{self.updates.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def prule := do
  let a ← number <* pchar '|'
  let b ← number
  return (a,b)
-- #eval AoCParser.parse prule "34|12"

def prules := do repeated (prule <* eol) <* eol
-- #eval AoCParser.parse prules "1|2\n3|5\n\n"

def pupdate := do separated number (pchar ',')

def pupdates := do separated pupdate eol
-- #eval AoCParser.parse pupdates "1 2 4\n5 6 9\n4 2"

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do Input.mk <$> prules <*> pupdates

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.updates.toList.filter
      (fun v ↦
        let occurs := v.toList.enumerate.map (fun (a, b) ↦ (b, a)) |> Std.HashMap.ofList
        input.rules.all (fun (a, b) ↦
          let i := occurs.get? a
          let j := occurs.get? b
          i == none || j == none || (i.unwrapOr 0) < (j.unwrapOr 0)))
    |>.map (fun l ↦ l[l.size / 2]!)
    |> sum

end Part1

namespace Part2

partial
def topologySort (rules: Array (Nat × Nat)) (l : List Nat) : List Nat :=
  let uppers := rules.filter (fun (a, b) ↦ (l.contains a) && (l.contains b)) |>.map (·.2)
  let lowers := rules.filter (fun (a, b) ↦ (l.contains a) && (l.contains b)) |>.map (·.1)
  let cands := lowers.filter (fun n ↦ !uppers.contains n)
         |> (Std.HashSet.ofArray ·)
         |>.toArray
  match cands with
   | #[] => l
    | #[top] => [top].append (topologySort rules (l.filter (· != top)))
    | _ => panic! s!"impossible {cands}"

def solve (input : Input) : Nat :=
  input.updates.toList.filter
      (fun v ↦
        let occurs := v.toList.enumerate.map (fun (a, b) ↦ (b, a)) |> Std.HashMap.ofList
        !input.rules.all (fun (a, b) ↦
          let i := occurs.get? a
          let j := occurs.get? b
          i == none || j == none || (i.unwrapOr 0) < (j.unwrapOr 0)))
    |>.map (topologySort input.rules ·.toList)
    |>.map (fun l ↦ l[l.length / 2]!)
    |> sum

end Part2

public def solve := AocProblem.config 2024 05 parser.parse Part1.solve Part2.solve

end Y2024.Day05
