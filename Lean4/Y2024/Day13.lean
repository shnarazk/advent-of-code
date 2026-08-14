module

public import Itertools
public meta import Itertools
public import WinnowParsers
public meta import WinnowParsers
public import «AoC».Basic
public meta import «AoC».Basic
public import «AoC».Combinator
-- public import «AoC».Vec

namespace Y2024.Day13

open Std

/-- The input data.
  - buttonA : Nat × Nat
  - buttonB : Nat × Nat
  - prize : Nat × Nat
-/
structure Input where
  buttonA : Nat × Nat
  buttonB : Nat × Nat
  prize : Nat × Nat

deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.buttonA}, {s.buttonB}, {s.prize}\n"

/- The input data format:

```
Button A: X+57, Y+16
Button B: X+20, Y+74
Prize: X=3288, Y=1772

Button A: X+51, Y+75
Button B: X+67, Y+15
Prize: X=2803, Y=2535
```
-/
namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

/-- Parse "Button A: X+57, Y+16\n" -/
def button (label : Char) : Parser (Nat × Nat) := do
 let _ ← pstring "Button " *> pchar label *> pstring ": X+"
 let x ← number <* pstring ", Y+"
 let y ← number <* eol
 pure (x, y)

#guard AoCParser.parse (button 'A') "Button A: X+57, Y+16\n" == some (57, 16)

/-- Parse "Prize: X=2803, Y=2535" -/
def prize : Parser (Nat × Nat) := do
 let x ← pstring "Prize: X=" *> number <* pstring ", Y="
 let y ← number <* eol
 pure (x, y)

def block : Parser Input := do
  let a ← button 'A'
  let b ← button 'B'
  let p ← prize
  pure <| Input.mk a b p

#guard AoCParser.parse prize "Prize: X=2803, Y=2535\n" == some (2803, 2535)

def parse : String → Option (Array Input) := AoCParser.parse parser
  where
    parser : Parser (Array Input) := do
    separated block eol

#guard AoCParser.parse number "123" == some 123

end parser

namespace Part1

def solve (_ : Array Input) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : Array Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2024 13
  ((CiCL.T dbg (fun data ↦ s!"got {data.unwrapOr #[] |>.size} items")) ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day13
