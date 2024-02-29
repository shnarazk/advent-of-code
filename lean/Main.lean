import «AoC»

def readData (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

def main : IO Unit := do
  IO.println s!"Hello, {hello}!"
  let lines ← readData "../data/2023/input-day01.txt"
  IO.println s!" => {lines}"
