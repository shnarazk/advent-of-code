module

public import «AoC».Basic
public import «AoC».Iterator
public import «AoC».Math
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

abbrev Vec := Array Int

instance : HAdd Vec Vec Vec where
  hAdd a b := (0... min a.size b.size).iter.map (fun i ↦ a[i]! + b[i]!) |>.toArray

#guard #[(1 : Int), 1, 3] + #[(3 : Int), 2, 5] == #[4, 3, 8]

instance : HSub Vec Vec Vec where
  hSub a b := (0... min a.size b.size).iter.map (fun i ↦ a[i]! - b[i]!) |>.toArray

#guard #[(1 : Int), 1, 3] - #[(3 : Int), 2, 5] == #[-2, -1, -2]
  
instance : HMul Vec Int Vec where
  hMul v n := v.iter.map (· * n) |>.toArray
  
#guard #[(1 : Int), 2, 3] * (3 : Int) == #[3, 6, 9]

/-- dot product of vectors -/
def dot (a b : Vec) : Int :=
  a.iter |>.zip b.iter |>.map (fun (a, b) ↦ a * b) |>.fold (· + ·) 0

#guard dot #[(1 : Int), 1, 3] #[(3 : Int), 2, 5] == 20

/-- erase the first column from the equation -/
def sweepOut (a b : Vec × Int) : Vec × Int :=
  let (av, as) := a
  let (bv, bs) := b
  let c := lcm av[0]! bv[0]!
  let ea := c / av[0]!
  let eb := c / bv[0]!
  let av' := av.drop 1
  let bv' := bv.drop 1
  (bv' * eb - av' * ea, bs * eb - as * eb)

-- #guard sweepOut (#[1, 1], 3) (#[3, 2], 5) == (#[-1], 2)

partial
def resolve (m : List (Vec × Int)) : Vec :=
  let v0 := m[0]!
  if m.length == 1 then
    #[v0.snd / v0.fst[0]!]
  else
    let (l1, l2) := m.iter.fold
      (fun (contains, notContains) (vec, total) ↦ if vec[0]! == 0
          then (contains.concat vec, notContains)
          else (contains, notContains.concat vec))
      ([], [])
    if l1.isEmpty
    then
      let m' := m |>.iter |>.map (fun (v, n) ↦ (v.drop 1, n)) |>.toList
      let effs := resolve m'
      #[0] ++ effs
    else
      let m' := m.drop 1 |>.iter |>.map (sweepOut v0 ·) |>.toList
      let effs := resolve m'
      let k := dot effs (v0.fst.drop 1)
      let ans := v0.snd / k
      #[ans] ++ effs
      
#guard resolve [(#[1], 3)] == #[3]

instance : HMul (Array Vec) Vec Vec where
  hMul buttons count := 
    count.iter.enumerate
    |>.fold
      (fun acc (i, n) ↦ acc + buttons[i]! * n)
      (Array.replicate buttons[0]!.size 0)
 
def solve (_ : Input) : Nat := 0

end Part2

public def solve := AocProblem.config 2025 10 parser.parse Part1.solve Part2.solve

end Y2025.Day10
