import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Parser

namespace Day10
open Std

structure Data where
  new ::
  grid : Array (Array Char)
deriving Repr

#eval #['a', 'b'].toList.toString
#eval #["aa", "bb"].foldl (fun x y => x ++ y) ""

 instance : ToString Data where
   toString self := self.grid.map (· |>.foldl String.push ""|>.append "\n")
      |>.foldl String.append ""

namespace parser
open Lean.Parsec AoCParser

def cell := pchar '|'
    <|> pchar '-'
    <|> pchar 'L'
    <|> pchar 'J'
    <|> pchar '7'
    <|> pchar 'F'
    <|> pchar '.'
    <|> pchar 'S'

def parser := do
  let cs ← many (many cell <* eol)
  return (Data.new cs)

end parser

namespace part1
def solve (data : String) : IO Unit := do
  match AoCParser.parse parser.parser data with
  | none   => IO.println s!"  part1: parse error"
  | some d => IO.println s!"  part1: {d}"
  return ()

end part1

namespace part2

def solve2_line (_line : String) : Nat := 0

-- #eval solve2_line ""

def solve (lines : Array String) : IO Unit := do
  let points : Array Nat := Array.map solve2_line lines
  let sum := Array.foldl (. + .) 0 points
  IO.println s!"  part2: {sum}"
  return ()
end part2

end Day10

def day10 (ext : Option String) : IO Unit := do
  let data ← dataOf 2023 10 ext
  let lines ← linesOf 2023 10 ext
  Day10.part1.solve data
  Day10.part2.solve lines
