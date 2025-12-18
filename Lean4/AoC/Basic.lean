module

public import Lean

@[expose] public section

/-- print a data like `dbg!` in Rust -/
def dbg {α : Type} [ToString α] (label : String) (a : α) : α :=
  dbgTrace s!"{label}: {a}" (fun _ ↦ a)

/-- return a path to the datafile of `year` and `day` -/
def dataFileName (year day : Nat) (ext : Option String): IO String := do
  let aoc_dir ← IO.getEnv "AOC_DIR"
  let d := ("0" ++ s!"{day}").takeEnd 2
  return match ext with
  | some ext => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}-{ext}.txt"
  | none     => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}.txt"

/-- return the content of `datafilename` -/
def readData (datafilename : String) : IO String := do
   IO.FS.readFile datafilename

-- #eval dataFileName 2023 2 none

/-- return file contents as String -/
def dataOf (year day : Nat) (ext : Option String): IO String :=
  dataFileName year day ext >>= readData

/-- return the lines of `datafilename` as an Arrat -/
def readLines (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

/-- return file contents as Array String -/
def linesOf (year day : Nat) (ext : Option String): IO (Array String) :=
  dataFileName year day ext >>= readLines

-- end FileIO

/-- Answers as pair of solutions -/
def Answers := String × String

/-- data representing a puzzle and its solutions -/
structure AocProblem where
  /-- year -/
  year : Nat
  /-- day -/
  day : Nat
  /-- a constraint on year -/
  validYear : 2000 < year
  /-- a constrain on day -/
  validDay : 1 ≤ day ∧ day ≤ 25
  /-- data file name -/
  input_name : String
  /-- a pair of answers or none before solving them -/
  answers: Option (String × String) := none
  /-- the total elapsed time to solve the both parts -/
  time: Float := 0
deriving BEq --, Repr
instance : ToString AocProblem where toString s := s!"Y{s.year}D{s.day}"

--#check AocProblem.mk 2024 8 (by simp)

namespace AocProblem

/-- constructor for `AoCProblem` -/
def new (year day : Nat) : AocProblem :=
  have valid_year : 2000 < max year 2001 := by
    have : 2001 ≤ max year 2001 := by exact Nat.le_max_right year 2001
    exact this
  have valid_day : 1 ≤ min (max day 1) 25 ∧ min (max day 1) 25 ≤ 25 := by
    constructor
    · have : 1 ≤ max day 1 := by exact Nat.le_max_right day 1
      have H : 1 ≤ 25 := by exact Nat.lt_of_sub_eq_succ rfl
      have : 1 ≤ min (max day 1) 25 := by exact Nat.le_min_of_le_of_le this H
      exact this
    · exact Nat.min_le_right (max day 1) 25
  AocProblem.mk
    (max year 2001)
    (min (max day 1) 25)
    valid_year
    valid_day
    ""
    none
    0

/-- return the input data file name -/
def fileName (self : AocProblem) (ext : Option String) : IO String :=
  dataFileName self.year self.day ext

/-- return the content of the input data file name -/
def getData (self : AocProblem) (ext : Option String) : IO String :=
  dataFileName self.year self.day ext >>= readData

/-- return the lines of the input data file name as an Array -/
def getLines (self : AocProblem) (ext : Option String) : IO (Array String) :=
  dataFileName self.year self.day ext >>= readLines

instance : Lean.ToJson AocProblem where
  toJson (s: AocProblem) :=
    Lean.Json.mkObj [
      ⟨"year", Lean.ToJson.toJson s.year⟩,
      ⟨"day", Lean.ToJson.toJson s.day⟩,
      ⟨"time", Lean.ToJson.toJson s.time⟩,
    ]

-- #eval Lean.ToJson.toJson (AocProblem.new 2024 10)

/-- return a JSON string representing `AoCProblem` -/
def toJson (self : AocProblem) : Lean.Json := Lean.ToJson.toJson self

/-- construct `AoCProblem` with the input and the solvers' oututs -/
def build {α β γ : Type} [ToString β] [ToString γ]
    (self : AocProblem)
    (parser : String → Option α)
    (solve₁ : α → β) (solve₂ : α → γ)
    (alt : Option String)
    : IO AocProblem := do
  if let some d := parser (← self.getData alt)
  then return { self with
    input_name := ← self.fileName alt
    answers := some (s!"{solve₁ d}", s!"{solve₂ d}") }
  else return { self with
    input_name := ← self.fileName alt
    answers := none }

/--
  Configure and build an `AocProblem` for the given Advent of Code `(year, day)`.

  Parameters:
  - `parser` should return `some data` on success, or `none` on parse failure.
    If parsing fails, the returned `AocProblem` will have `answers := none`.
  - `solve₁` and `solve₂` compute part 1 and part 2 results from the parsed input.
  - `alt` selects an alternate input filename suffix (see `dataFileName`), e.g.
    `some "sample"` to load `.../input-dayDD-sample.txt`, or `none` for the default.

  Returns:
  An `IO AocProblem` with fields `input_name` set to the resolved filename and
  `answers` populated on successful parsing.

  Example:
  `AocProblem.config 2024 1 parse solve1 solve2 (some "sample")`
-/
def config {α β γ : Type} [ToString β] [ToString γ]
    (year day : Nat)
    (parser : String → Option α)
    (solve₁ : α → β) (solve₂ : α → γ)
    (alt : Option String)
    : IO AocProblem := do
  AocProblem.new year day |>.build parser solve₁ solve₂ alt

end AocProblem

/-- Return an array consisting of elements in `a` -/
def unique {α : Type} (a : Array α) [BEq α] [Hashable α] : Array α :=
  let hash := Array.foldl (·.insert ·) (Std.HashSet.emptyWithCapacity : Std.HashSet α) a
  hash.toArray

-- #eval unique #[1, 0, 2, 1, 3, 2]

/-- a class for monoidal operations on containers of numbers -/
class Accumulation (α : Type) where
  /-- summention -/
  sum    : α → Nat
  /-- product -/
  product: α → Nat

instance : Accumulation (List Nat) where
  sum     a := a.foldl Nat.add 0
  product a := a.foldl Nat.mul 1

instance : Accumulation (List (Option Nat)) where
  sum     a := a.filterMap (·) |>.foldl Nat.add 0
  product a := a.filterMap (·) |>.foldl Nat.mul 1

instance : Accumulation (List Int) where
  sum     a := a.foldl Int.add 0 |>.toNat
  product a := a.foldl Int.mul 1 |>.toNat

instance : Accumulation (List (Option Int)) where
  sum     a := a.filterMap (·) |>.foldl Int.add 0 |>.toNat
  product a := a.filterMap (·) |>.foldl Int.mul 1 |>.toNat

instance : Accumulation (Array Nat) where
  sum     a := a.foldl Nat.add 0
  product a := a.foldl Nat.mul 1

instance : Accumulation (Array (Option Nat)) where
  sum     a := a.filterMap (·) |>.foldl Nat.add 0
  product a := a.filterMap (·) |>.foldl Nat.mul 1

instance : Accumulation (Array Int) where
  sum     a := a.foldl Int.add 0 |>.toNat
  product a := a.foldl Int.mul 1 |>.toNat

instance : Accumulation (Array (Option Int)) where
  sum     a := a.filterMap (·) |>.foldl Int.add 0 |>.toNat
  product a := a.filterMap (·) |>.foldl Int.mul 1 |>.toNat

-- open Accumulation

-- #eval Accumulation.sum [1, 3, 5]
-- #eval sum [1, 3, 5]
-- #eval product [1, 3, 5]

/-- Rusty enumerate -/
def List.enumerate {α : Type} (a : List α) : List (Nat × α) := a.zipIdx.map (fun (x, i) => (i, x))
-- List.zip (List.range a.length) a
-- #eval [2, 4, 5].enum
-- #eval [2, 4, 5].enumerate

/-- alias of Array.enumerate. -/
def Array.enum {α : Type} (a : Array α) : Array (Nat × α) :=
  a.zipIdx.map (fun (x, i) ↦ (i, x))

-- example : #[2, 4, 5].enum = #[(0, 2), (1, 4), (2, 5)] := rfl

/-- Rusty enumerate -/
def Array.enumerate {α : Type} (a : Array α) : Array (Nat × α) := Array.enum a

-- #eval #[2, 4, 5].enum

/-- enumerate on a `String` as `Array Char` -/
def String.enum (a : String) : List (Nat × Char) :=
  List.zip (List.range a.length) a.toList

/-- deprecated version of `String.enum` -/
@[deprecated "Use `String.enum` instead of 'String.enumerate`" (since := "2024-11-01")]
def String.enumerate := String.enum

namespace Option

/--
- `(some "abc").mapOr (·.length) 99 => 3`
- `none.mapOr (·.length) 99 => 99`

`map_or` is already used for a prep
-/
def mapOr {α β : Type} : (Option α) → (f : α → β) → (default : β) → β
  | some a, f, _ => f a
  | none, _, default => default

-- #eval some "abc" |>.mapOr (·.length) 99
-- #eval none |>.mapOr (·.length) 99

/--
- (some "abc").unwrapOr "." => "abc"
- none.unwrapOr "." => "."

imported from Rust
-/
def unwrapOr {α : Type} : (Option α) → (default : α) → α
  | some a, _ => a
  | none , df => df

end Option

/-- Rusty operation -/
def Bool.map {α : Type} (self : Bool) (f : Unit → α) : Option α :=
  match self with
  | true  => some (f ())
  | false => none
-- #eval true.map (K 3)

/-- Rusty operation -/
def Bool.then {α : Type} (self : Bool) (f : Unit → Option α) : Option α :=
  match self with
  | true  => f ()
  | false => none

/-- Do the same with `windows(2)` in Rust -/
def List.windows2 {α : Type} (l : List α) : List (α × α) :=
  List.zip l.dropLast l.tail
example : (List.range 4 |>.windows2) = [(0, 1), (1, 2), (2, 3)] := by rfl

/-- Do the same with `windows(2)` in Rust -/
def Array.windows2 {α : Type} (a : Array α) : List (α × α) :=
  let l := a.toList
  List.zip l.dropLast l.tail
-- example : (Array.range 4 |>.windows2) = [(0, 1), (1, 2), (2, 3)] := by rfl

/-- Type `\^-` to insert it. This isn't the high-minus `¯` used in BQN. -/
prefix:max "⁻" => Neg.neg
example : 4 + ⁻2 = 2 := by rfl
example : (· + ·) 1 ⁻8 = -7 := by rfl
