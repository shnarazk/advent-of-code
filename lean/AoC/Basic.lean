
def dataFileName (year day : Nat) : String :=
  s!"../data/{year}/input-day{d}.txt"
  where
    d := ("0" ++ s!"{day}").takeRight 2

#eval dataFileName 2023 2

def readData (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

def dataFor (year day : Nat) : IO (Array String) :=
  pure (dataFileName year day) >>= readData
