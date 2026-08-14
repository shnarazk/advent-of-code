module

public import Itertools
-- public meta import Itertools
public import WinnowParsers
public meta import WinnowParsers
public import «AoC».Basic
public meta import «AoC».Basic
public import «AoC».Combinator

namespace Y2024.Day13

open Std

/-- The input data.
  - buttonA : Nat × Nat
  - buttonB : Nat × Nat
  - prize   : Nat × Nat
-/
structure Input where
  buttonA : Nat × Nat
  buttonB : Nat × Nat
  prize   : Nat × Nat
deriving BEq, Hashable, Repr

instance : ToString Input where
  toString s := s!"{s.buttonA}, {s.buttonB}, {s.prize}\n"

def Input.solver (self : Input) (offset : Nat := 0) : Nat :=
  let dist (a b : Nat) : Nat := if a >= b then a - b else b - a
  let a := self.buttonA
  let b := self.buttonB
  let goal := CoP.both2 (· + ·) self.prize (offset, offset)
  if a.2 * b.1 != a.1 * b.2 then
      let tmp1 := dist (a.2 * b.1) (a.1 * b.2)
      let tmp2 := dist (b.1 * goal.2) (b.2 * goal.1)
      let tmp3 := dist (a.2 * goal.1) (a.1 * goal.2)
      let i := tmp2 / tmp1
      let im := tmp2 % tmp1
      let j := tmp3 / tmp1
      let jm := tmp3 % tmp1
      if im == 0 && jm == 0 then 3 * i + j else 0
    else
      0

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
    parser : Parser (Array Input) := separated block eol

end parser

namespace Part1

def solve (input : Array Input) : Nat := input.iter |>.map (·.solver) |>.sum

end Part1

namespace Part2

def solve (input : Array Input) : Nat :=
  input.iter |>.map (·.solver 10_000_000_000_000) |>.sum

end Part2

public def solve := AocProblem.config 2024 13 parser.parse Part1.solve Part2.solve

end Y2024.Day13
