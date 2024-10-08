import Lean
import «AoC».Mat1

-- namespace FileIO
/--
Build and return a data filename
-/
def dataFileName (year day : Nat) (ext : Option String): IO String := do
  let aoc_dir ← IO.getEnv "AOC_DIR"
  let d := ("0" ++ s!"{day}").takeRight 2
  return match ext with
  | some ext => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}-{ext}.txt"
  | none     => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}.txt"


def readData (datafilename : String) : IO String := do
     IO.FS.readFile datafilename

-- #eval dataFileName 2023 2 none
/--
return file contents as String
-/
def dataOf (year day : Nat) (ext : Option String): IO String :=
  dataFileName year day ext >>= readData

def readLines (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

/--
return file contents as Array String
-/
def linesOf (year day : Nat) (ext : Option String): IO (Array String) :=
  dataFileName year day ext >>= readLines

-- end FileIO

def Answers := String × String

structure AocProblem where
  year : Nat
  day : Nat
  validYear : 2000 < year
  validDay : 1 ≤ day ∧ day ≤ 25
deriving BEq, Repr
instance : ToString AocProblem where toString s := s!"Y{s.year}D{s.day}"

namespace AocProblem

def fileName (self : AocProblem) (ext : Option String) : IO String :=
  dataFileName self.year self.day ext

def getData (self : AocProblem) (ext : Option String) : IO String :=
  dataFileName self.year self.day ext >>= readData

def getLines (self : AocProblem) (ext : Option String) : IO (Array String) :=
  dataFileName self.year self.day ext >>= readLines

end AocProblem

/--
Return an array consisting of elements in `a`
-/
def unique (a : Array α) [BEq α] [Hashable α] : Array α :=
  let hash := Array.foldl (·.insert ·) (Std.HashSet.empty : Std.HashSet α) a
  hash.toArray

-- #eval unique #[1, 0, 2, 1, 3, 2]

class Accumulation (α : Type) where
  sum    : α → Nat
  product: α → Nat

instance : Accumulation (List Nat) where
  sum     a := a.foldl Nat.add 0
  product a := a.foldl Nat.mul 1

instance : Accumulation (List Int) where
  sum     a := Int.toNat <| a.foldl Int.add 0
  product a := Int.toNat <| a.foldl Int.mul 1

instance : Accumulation (Array Nat) where
  sum     a := a.foldl Nat.add 0
  product a := a.foldl Nat.mul 1

instance : Accumulation (Array Int) where
  sum     a := Int.toNat <| a.foldl Int.add 0
  product a := Int.toNat <| a.foldl Int.mul 1

open Accumulation

-- #eval Accumulation.sum [1, 3, 5]
-- #eval sum [1, 3, 5]
-- #eval product [1, 3, 5]

def List.enumerate (a : List α) : List (Nat × α) := List.zip (List.range a.length) a

-- #eval [2, 4, 5].enumerate

def Array.enumerate (a : Array α) : Array (Nat × α) := Array.zip (Array.range a.size) a

-- #eval #[2, 4, 5].enumerate
