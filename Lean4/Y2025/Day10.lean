module

public import Itertools
public import WinnowParsers
public meta import WinnowParsers
public import «AoC».Basic
public meta import «AoC».Basic
public import «AoC».Math
public meta import «AoC».Math

abbrev Vec := Array Int

-- for debug
instance : Std.ToFormat Ordering where
  format o := match o with
    | .lt => "lt"
    | .eq => "eq"
    | .gt => "gt"

class ToVec (α : Type) (β : outParam Type) where
  toVec : α → β

instance : ToVec Nat Int where
  toVec (n : Nat) : Int := n.toInt64.toInt

instance {α β : Type} [ToVec α β] : ToVec (Array α) (Array β) where
  toVec v := v.iter.map ToVec.toVec |>.toArray

#guard ToVec.toVec #[1, 2] == #[(1 : Int), 2]
#guard ToVec.toVec #[#[1, 2]] == #[#[(1 : Int), 2]]
#guard ToVec.toVec #[#[#[1], #[2]]] == #[#[#[(1 : Int)], #[2]]]

/-- rank-polymorphic toInt -/
def Nat.inted (n : Nat) : Int := ToVec.toVec n
def Array.inted {α β : Type} [ToVec α β] (v : Array α) : Array β := ToVec.toVec v

#guard (3 : Nat).inted == (3 : Int)
#guard #[1, 2].inted == #[(1 : Int), 2]
#guard #[#[1, 2]].inted == #[#[(1 : Int), 2]]
#guard #[#[#[1], #[2]]].inted == #[#[#[(1 : Int)], #[2]]]

namespace Y2025.Day10

structure Input where
  line : Array (Array Bool × Array (Array Nat) × Array Nat)
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.line}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec.String

def parse_indicators := do
  let v ← pchar '[' *> repeated (pchar '.' <|> pchar '#') <* pchar ']'
  v.iter.map (· == '#') |>.toArray |> pure

#guard parse parse_indicators "[..#.]" == some #[false, false, true, false]

def parse_nums := separated number (pchar ',')

#guard parse parse_nums "42,31,8" == some #[42, 31, 8]

def parse_buttons := separated (pchar '(' *> parse_nums <* pchar ')') (pchar ' ')

#guard parse parse_buttons "(42,31) (4,31)" == some #[#[42, 31], #[4, 31]]

def parse_requirement := pchar '{' *> parse_nums <* pchar '}'

#guard parse parse_requirement "{42,31,4,31}" == some #[42, 31, 4, 31]

def parse_line := do
  let i ← parse_indicators <* pchar ' '
  let b ← parse_buttons <* pchar ' '
  let r ← parse_requirement
  return (i, b, r)

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := do Input.mk <$> separated parse_line eol

#guard parse "[.#] (1,0) (2,4) {4,3}"
    == some { line := #[(#[false, true], #[#[1, 0], #[2, 4]], #[4, 3])]}

end parser

namespace Part1

open Std

def toIdicator (buttons : Array (Array Nat)) (state : Array Bool) (len : Nat) : Array Bool :=
  state.iter
    |>.enumerate
    |>.fold
      (fun acc (n, b) ↦
        if b then buttons[n]!.iter.fold (fun acc i ↦ acc.modify i (!·)) acc else acc)
      (Array.replicate len false)

#guard toIdicator #[#[1], #[0,2]] #[false, true] 3 == #[true, false, true]

def solve' (setting : Array Bool × Array (Array Nat) × Array Nat) : Nat := Id.run do
  let (indicator, buttons,_ ) := setting
  let len := indicator.size
  let mut toVisit : Array (Array Bool) := #[Array.replicate buttons.size false]
  while !toVisit.isEmpty do
    let mut next : HashSet (Array Bool) := HashSet.emptyWithCapacity 1
    for state in toVisit.iter do
      if toIdicator buttons state len == indicator then return (state.iter.filter (·) |>.length)
      for (i, b) in state.iter.enumerate do
        if b then continue
        let s := state.set! i true
        next := next.insert s
    toVisit := next.toArray
  10000

def solve (input : Input) : Nat := input.line.iter |>.map solve' |>.sum

end Part1

namespace Part2

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
@[inline]
def dot (a b : Vec) : Int :=
  a.iter |>.zip b.iter |>.map (fun (a, b) ↦ a * b) |>.fold (· + ·) 0

#guard dot #[(1 : Int), 1, 3] #[(3 : Int), 2, 5] == 20

/-- erase the first column from the equation -/
@[inline]
def sweepOut (a b : Vec × Int) : Vec × Int :=
  let (av, as) := a
  let (bv, bs) := b
  let c := lcm av[0]! bv[0]!
  let ea := c / av[0]!
  let eb := c / bv[0]!
  let av' := av.drop 1
  let bv' := bv.drop 1
  (bv' * eb - av' * ea, bs * eb - as * eb)

#guard sweepOut (#[1, 1], 3) (#[3, 2], 5) == (#[-1], 2)

partial
def resolve (m : List (Vec × Int)) : Vec :=
  let v0 := m[0]!
  if m.length == 0 then
    #[]
  else if m.length == 1 then
    #[v0.snd / v0.fst[0]!]
  else
    let (l1, l2) := m.iter.fold
      (fun (contains, notContains) line ↦ if line.fst[0]! == 0
          then (contains.concat line, notContains)
          else (contains, notContains.concat line))
      ([], [])
    if l1.isEmpty then
      let m' := m |>.iter |>.map (fun (v, n) ↦ (v.drop 1, n)) |>.toList
      let effs := resolve m'
      #[0] ++ effs
    else
      let v0 := l1[0]!
      let m' := (l1.drop 1 ++ l2).drop 1 |>.iter |>.map (sweepOut v0 ·) |>.toList
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

def upperLimits₁ (buttons : Array (Array Nat)) (goal : Array Nat) : Array Nat :=
  buttons.iter
    |>.map (·.iter.map (goal[·]!) |>.fold min (goal.max?.unwrapOr 0) |> (· + 1))
    |>.toArray

#guard upperLimits₁ #[#[0, 1], #[1, 2]] #[2, 5, 6] == #[3, 6]

def lowerLimits (buttons : Array (Array Nat)) (goal : Array Nat) : Array Nat := Id.run do
  let mut affectors : Array (Array Nat) := Array.ofFn (n := goal.size) (fun _ ↦ #[])
  for (target, b_id) in buttons.zipIdx.iter do
    for light_id in target do
      affectors := affectors.modify light_id (·.push b_id)
  let mut result : Array Nat := Array.ofFn (n := buttons.size) (fun _ ↦ 0)
  for (bs, light_id) in affectors.zipIdx.iter do
    if bs.size == 1 then
      result := result.set! bs[0]! goal[light_id]!
  result

#guard lowerLimits #[#[0, 1], #[2]] #[4, 2, 6] == #[2, 6]

/-- orderの下で各buttonによって値が確定するlight
- Rustの `final_affectors`をrename
-/
def fixLights (buttons : Array (Array Nat)) (order : Array Nat) (numLights : Nat)
    : Array (Array Nat) := Id.run do
  let mut lastAffector : Array Nat := Array.ofFn (n := numLights) (fun _ ↦ 0)
  for buttonId in order.iter do
    for lightId in buttons[buttonId]!.iter do
      lastAffector := lastAffector.set! lightId buttonId
  Array.range buttons.size
    |>.iter
    |>.map (fun buttonId ↦
        lastAffector.zipIdx.iter.filter (·.fst == buttonId) |>.map Prod.snd |>.toArray )
    |>.toArray

#guard fixLights #[#[0, 1], #[2], #[0, 2]] #[0, 1, 2] 3 == #[#[1], #[], #[0, 2]]

/-- Return `Odering` compared with the `goal`
- Rustの `compare`をrename
-/
def reachability (flips goal : Array Nat) : Ordering := Id.run do
  let mut ord := Ordering.eq
  for (f, g) in (flips.zip goal).iter do
    match compare f g with
    | .gt => return .gt
    | .lt => ord := .lt
    | _ => ()
  ord

#guard reachability #[3, 0, 4] #[3, 2, 1] = .gt
#guard reachability #[3, 2, 4] #[3, 2, 4] = .eq

/--
- Rustの`button_order`をrename
-/
def buttonOrdering (a b : Float × Nat) : Ordering :=
  if a.fst = b.fst
  then compare a.snd b.snd
  else if a.fst < b.fst then .lt else .gt

def bestButtonOrder (buttons : Array (Array Nat)) (affectors' : Array Vec) : Array Nat := Id.run do
  let fMax :Float := 10_000_000.0
  let numButtons := buttons.size
  let mut result : Array Nat := #[]
  let mut affectors := affectors'
  for _ in 0 ... numButtons do
    let mut buttonWeights : Array Float := Array.ofFn (n := numButtons) (fun _ ↦ 0.0)
    for (affectingLights, bId) in buttons.zipIdx.iter do
      if result.contains bId then
        buttonWeights := buttonWeights.set! bId fMax
        continue
      let mut occr := fMax
      for lId in affectingLights.iter do
        if affectors[lId]!.contains bId then
          let value : Float := affectors[lId]!.size.toFloat
          if value < occr then
            occr := value
        buttonWeights := buttonWeights.set! bId occr
    let tmp : Array (Float × Nat) := buttonWeights.zipIdx.qsort (buttonOrdering · · == .lt)
    let theButton : Nat := tmp[0]!.snd
    result := result.push theButton
    affectors := affectors.iter |>.map (·.erase theButton) |>.toArray
  result

#guard bestButtonOrder #[#[1], #[0], #[0, 1]] #[#[1, 2], #[0, 2]] == #[0, 2, 1]

def solveRec
    (level best' : Nat)
    (button_toggles' : Array Nat)
    (orderToIndex : Array Nat)
    (finalAffector : Array (Array Nat))
    (availabeBands : Array (Nat × Nat))
    (buttons : Array (Array Nat))
    (goal : Array Nat)
    : Nat := Id.run do
  if level ≥ buttons.size then return best'
  let index : Nat := orderToIndex[level]!
  let mut best := best'
  let mut buttonToggles := button_toggles'
  let mut lightFlips : Array Nat := Array.ofFn (n := goal.size) (fun _ ↦ 0)
  for i in orderToIndex.iter.take level do
    for lightId in buttons[i]!.iter do
      lightFlips := lightFlips.modify lightId (· + buttonToggles[i]!)
  for lightId in buttons[index]!.iter do
      lightFlips := lightFlips.modify lightId (· + availabeBands[index]!.snd)
  -- next_value
  let band := availabeBands[index]!.snd - availabeBands[index]!.fst
  for numToggles' in 0 ... band do
    let numToggles := availabeBands[index]!.snd - 1 - numToggles'
    -- - some true  : break 'next_value
    -- - some false : continue 'next_value
    let mut skipToNextValue : Option Bool := none
    buttonToggles := buttonToggles.set! index numToggles
    for lightId in buttons[index]!.iter do
      lightFlips := lightFlips.modify lightId (· - 1)
    for lightId in finalAffector[index]!.iter do
      match compare lightFlips[lightId]! goal[lightId]! with
      | .lt => skipToNextValue := some true
      | .eq => ()
      | .gt => if skipToNextValue.isNone then skipToNextValue := some false
    match /- dbg s!"   {buttonToggles}: {lightFlips}" -/ skipToNextValue with
    | some true => break
    | some false => continue
    | _ => ()
    let ans := buttonToggles.sum
    if ans ≥ best then continue
    match /- (fun a ↦ dbg f!"{level}/{index}{buttonToggles}: {lightFlips} {a}" a) <| -/ reachability lightFlips goal with
    | .lt =>
      best := solveRec
          (level + 1)
          best
          buttonToggles
          orderToIndex
          finalAffector
          availabeBands
          buttons
          goal
        |> (min · best)
    | .eq => if ans < best then best := dbg s!"improved {ans}" ans
    | .gt => continue
  best
termination_by buttons.size - level

def solve' (buttons : Array (Array Nat)) (goal : Array Nat) : Nat := Id.run do
  let numButtons := buttons.size
  let numLights := goal.size
  let mut affectors : Array Vec := Array.ofFn (n := numLights) (fun _ ↦ #[])
  for (lights, bId) in buttons.zipIdx.iter do
    for lId in lights.iter do
      affectors := affectors.modify lId (·.push bId)
  let availableBands := Array.zip (lowerLimits buttons goal) (upperLimits₁ buttons goal)
  let orderToIndex := bestButtonOrder buttons affectors
  let finalAffector := fixLights buttons orderToIndex numLights
  let buttonToggles := Array.ofFn (n := numButtons) (fun _ ↦ 0)
  solveRec
    0
    1_000_000_000
    buttonToggles
    (dbg s!"orderToIndex: {orderToIndex}" orderToIndex)
    finalAffector
    (dbg s!"availableBands:{availableBands}" availableBands)
    buttons
    (dbg s!"goal: {goal}" goal)


def solve (input : Input) : Nat :=
  input.line.iter
    |>.map (fun (_, b, r) ↦ solve' b r)
    |>.sum

end Part2

public def solve := AocProblem.config 2025 10 parser.parse Part1.solve Part2.solve

end Y2025.Day10
