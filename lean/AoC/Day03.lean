import Std
import «AoC».Basic

namespace Day03

def asterisks (lines : Array String) : List (Nat × Nat) :=
  lines.foldl (fun (i, l) line =>
      (i + 1, line.foldl (fun (j, l) ch =>
          (j + 1, if ch == '.' || ch.isDigit then l else l ++ [(i, j)]))
        (0, l)
      |>.snd))
    ((0, []) : Nat × List (Nat × Nat))
  |>.snd

def solve1 (lines : Array String) : IO Unit := do
  let points := dbgTraceVal $ asterisks lines
  let sum := points.length -- Array.foldl (. + .) 0 points
  IO.println s!"  part1: {sum}"
  return ()

def solve2_line (_line : String) : Nat := 0

def solve2 (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!"  part2: {sum}"
  return ()

end Day03

def day03 (ext : Option String): IO Unit := do
  let data ← linesOf 2023 3 ext
  pure data >>= Day03.solve1
  pure data >>= Day03.solve2
