module

public import «AoC».Basic
public import «AoC».Iterator
public import «AoC».Parser

namespace Y2025.Day11

open Std

structure Input where
  names : Array String
  flow : HashMap String (Array String)
deriving BEq, Repr

instance : ToString Input where toString s := s!"{s.names.size}, {s.flow.toList}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_name := alphabets
def parse_line := do
  let node ← parse_name <* pstring ": "
  let outputs ← separated parse_name whitespaces
  pure (node, outputs)

-- #eval AoCParser.parse parse_line "abv: qqq rew "

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do
    let ar ← separated parse_line eol
    pure <| Input.mk (ar.iter.map (·.fst) |>.toArray) ar.iter.toHashMap

end parser

namespace Part1

partial
def traverse
    (map : HashMap String (Array String))
    (table' : HashMap (String × String) Nat)
    (src dst : String)
    : Nat × HashMap (String × String) Nat := Id.run do
  match table'.get? (src, dst) with
  | some n => return (n, table')
  | none =>
    let mut table := table'
    let mut pathes := 0
    for dest in map.get! src do
      let (c, t) := traverse map table dest dst
      pathes := pathes + c
      table := t
    (pathes, table.insert (src, dst) pathes)

def solve (input : Input) : Nat := Id.run do
  let mut count : HashMap (String × String) Nat := HashMap.emptyWithCapacity input.names.size
  for (s, ds) in input.flow do
    for d in ds do
      count := count.insert (s, d) 1
  traverse input.flow count "you" "out" |>.fst

end Part1

namespace Part2

partial
def traverse
    (map : HashMap String (Array String))
    (table' : HashMap (String × String) Nat)
    (src dst : String)
    : Nat × HashMap (String × String) Nat := Id.run do
  match table'.get? (src, dst) with
  | some n => return (n, table')
  | none =>
    let mut table := table'
    let mut pathes := 0
    let some dests := map.get? src | return (0, table)
    for dest in dests do
      let (c, t) := traverse map table dest dst
      pathes := pathes + c
      table := t
    (pathes, table.insert (src, dst) pathes)

def solve (input : Input) : Nat := Id.run do
  let mut count : HashMap (String × String) Nat := HashMap.emptyWithCapacity input.names.size
  for (s, ds) in input.flow do
    for d in ds do
      count := count.insert (s, d) 1
  let (fft_dac, count') := traverse input.flow count "fft" "dac"
  count := count'
  let (dac_fft, count') := traverse input.flow count "dac" "fft"
  count := count'
  match fft_dac == 0, dac_fft == 0 with
  | false, false => return (panic s!"unexpected: {fft_dac}, {dac_fft}")
  | false, true =>
      let (svr_fft, count') := traverse input.flow count "svr" "fft"
      count := count'
      let (dac_out, _) := traverse input.flow count "dac" "out"
      return svr_fft * fft_dac * dac_out
  | true, false =>
      let (svr_dac, count') := traverse input.flow count "svr" "dac"
      count := count'
      let (fft_out, _) := traverse input.flow count "fft" "out"
      return svr_dac * dac_fft * fft_out
  | true, true => return (dbg s!"??" 0)

end Part2

public def solve := AocProblem.config 2025 11 parser.parse Part1.solve Part2.solve

end Y2025.Day11
