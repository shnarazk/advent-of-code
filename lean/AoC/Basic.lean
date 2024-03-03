/--
Build and retrun a data filename
-/
def dataFileName (year day : Nat) (ext : Option String): IO String := do
  let aoc_dir ← IO.getEnv "AOC_DIR"
  let d := ("0" ++ s!"{day}").takeRight 2
  return match ext with
  | some ext => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}-{ext}.txt"
  | none     => s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}.txt"

-- #eval dataFileName 2023 2 none

def readData (datafilename : String) : IO String := do
     IO.FS.readFile datafilename

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

def color.red     : String := "\x1B[001m\x1B[031m"
def color.green   : String := "\x1B[001m\x1B[032m"
def color.blue    : String := "\x1B[001m\x1B[034m"
def color.magenta : String := "\x1B[001m\x1B[035m"
def color.cyan    : String := "\x1B[001m\x1B[036m"
def color.reset   : String := "\x1B[000m"
def color.revert  : String := "\x1B[1A\x1B[1G\x1B[1K"
def color.reverse : String := "\x1B[001m\x1B[07m"
