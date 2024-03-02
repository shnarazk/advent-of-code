/-
Build and retrun a data filename
-/
def dataFileName (year day : Nat) (ext : Option String): IO String := do
  let aoc_dir ← IO.getEnv "AOC_DIR"
  let d := ("0" ++ s!"{day}").takeRight 2
  return match ext with
  | some ext => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}-{ext}.txt"
  | none     => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}.txt"

#eval dataFileName 2023 2 none

def readData (datafilename : String) : IO String := do
     IO.FS.readFile datafilename

def dataOf (year day : Nat) (ext : Option String): IO String :=
  dataFileName year day ext >>= readData

def readLines (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

def linesOf (year day : Nat) (ext : Option String): IO (Array String) :=
  dataFileName year day ext >>= readLines
