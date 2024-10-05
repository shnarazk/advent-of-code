import Batteries
import «AoC».Basic

namespace Y2024.Day01
open Accumulation

namespace Part1

def solve (_lines : Array String) : Nat := 0

end Part1

namespace Part2

def solve (_lines : Array String) : Nat := 0

end Part2

protected def solve (alt : Option String): IO Answers := do
  let lines ← linesOf 2024 1 alt
  return (s!"{Y2024.Day01.Part1.solve lines}", s!"{Y2024.Day01.Part2.solve lines}")

end Y2024.Day01

