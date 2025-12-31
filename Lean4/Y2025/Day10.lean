module

public import «AoC».Basic
public import «AoC».Iterator
public import «AoC».Parser

namespace Y2025.Day10

structure Input where
  line : Array (Array Bool × Array (Array Nat) × Array Nat)
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_indicators := do
  let v ← pchar '[' *> repeated (pchar '.' <|> pchar '#') <* pchar ']'
  v.iter.map (· == '#') |>.toArray |> pure
-- #eval AoCParser.parse parse_indicators "[..##.]"

def parse_nums := separated number (pchar ',') 
-- #eval AoCParser.parse parse_nums "42,31,8"

def parse_buttons := separated (pchar '(' *> parse_nums <* pchar ')') (pchar ' ') 
-- #eval AoCParser.parse parse_buttons "(42,31) (4,31)"

def parse_requirement := pchar '{' *> parse_nums <* pchar '}'
-- #eval AoCParser.parse parse_requirement "{42,31,4,31}"

def parse_line := do
  let i ← parse_indicators <* pchar ' '
  let b ← parse_buttons <* pchar ' '
  let r ← parse_requirement
  return (i, b, r)

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do Input.mk <$> separated parse_line eol
-- #eval parse "[.#] (1,3) (2,3,4) {42,31,4,31}"

end parser

namespace Part1

open Std

def toIdicator (buttons : Array (Array Nat)) (state : Array Bool) (len : Nat) : Array Bool :=
  state.iter
    |>.enumerate
    |>.fold
      (fun acc (n, b) ↦
        if b then buttons[n]! |>.iter |>.fold (fun acc i ↦ acc.modify i (!·)) acc else acc)
      (Array.replicate len false)
 -- #eval toIdicator #[#[1], #[0,2]] #[false, true] 3

def solve' (setting : Array Bool × Array (Array Nat) × Array Nat) : Nat := Id.run do
  let (indicator, buttons,_ ) := setting
  let len := indicator.size
  let mut toVisit : Array (Array Bool) := #[Array.replicate buttons.size false]
  while !toVisit.isEmpty do
    let mut next : HashSet (Array Bool) := HashSet.emptyWithCapacity 1
    for state in toVisit.iter do
      if toIdicator buttons state len == indicator then return (state.iter.filter (·) |>.count)
      for (i, b) in state.iter.enumerate do
        if b then continue
        let s := state.set! i true
        next := next.insert s
    toVisit := next.toArray
  10000

def solve (input : Input) : Nat := input.line.iter |>.map solve' |>.sum

end Part1

namespace Part2

instance : HAdd (Array Int) (Array Int) (Array Int) where
  hAdd a b := (0... min a.size b.size).iter.map (fun i ↦ a[i]!) |>.toArray
  
instance : HMul (Array Int) Int (Array Int) where
  hMul v n := v.iter.map (· * n) |>.toArray

instance : HMul (Array (Array Int)) (Array Int) (Array Int) where
  hMul buttons count := 
    count.iter.enumerate
    |>.fold
      (fun acc (i, n) ↦ acc + buttons[i]! * n)
      (Array.replicate buttons[0]!.size 0)
 
def solve (_ : Input) : Nat := 0

end Part2

public def solve := AocProblem.config 2025 10 parser.parse Part1.solve Part2.solve

end Y2025.Day10
