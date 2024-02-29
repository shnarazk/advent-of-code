def dataFileName (year day : Nat) : IO String := do
  let aoc_dir ← IO.getEnv "AOC_DIR"
  let d := ("0" ++ s!"{day}").takeRight 2
  return s!"{aoc_dir.getD ".."}/data/{year}/input-day{d}.txt"

#eval dataFileName 2023 2

def readData (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

def dataFor (year day : Nat) : IO (Array String) :=
  dataFileName year day >>= readData
