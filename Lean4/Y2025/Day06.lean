module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2025.Day06
open Accumulation CiCL

inductive Op where
  | add
  | mul
deriving BEq, Hashable, Repr

instance : ToString Op where
  toString : Op → String
    | .add => "+"
    | .mul => "*"

structure Input where
  problems : Array (Array Nat)
  ops : Array Op
  data : String
deriving BEq, Hashable, Repr

instance : ToString Input where toString s := s!"{s.problems} {s.ops} {s.data.length}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_values : Parser (Array Nat) := whitespaces? *> separated number whitespaces <* whitespaces?
def parse_part1 : Parser (Array (Array Nat)) := separated parse_values eol
def parse_op : Parser Op := do pchar '+' *> pure Op.add <|> pchar '*' *> pure Op.mul
def parse_ops : Parser (Array Op) := whitespaces? *> separated parse_op whitespaces

def parse (str : String) : Option Input := AoCParser.parse parser str
  where
    parser : Parser Input := do
      let problems ← parse_part1 <* eol
      let ops ← parse_ops
      pure <| Input.mk problems ops str

end parser

namespace Part1

def solve (input : Input) : Nat :=
  input.ops.iter.enumerate
    |>.map (fun (i, op) => match op with
      | .add => input.problems.map (·[i]!) |>.sum
      | .mul => input.problems.map (·[i]!) |>.foldl (· * ·) 1)
    |>.fold (· + ·) 0

end Part1

namespace Part2

open Option

def solve (input : Input) : Nat := Id.run do
  let slices := input.data |>.split '\n' |>.filter (!·.isEmpty)
  let lines := slices |>.map (fun s ↦ s.chars.toArray)
  let num_lines := slices.count
  let lastLine := slices |>.toList |>.getLast! |>.toString
  let columnStarts := lastLine.toList.iter 
    |>.enumerate
    |>.filterMap (fun (i, c) ↦ (c != ' ').map (fun _ ↦ i))
    |>.toList
    |>.concat (lastLine.length + 1)
  let mut total := 0
  for range in columnStarts.windows2.iter do
    let mul? := (· == '*') <| String.Pos.Raw.get! lastLine ⟨range.fst⟩
    let mut c := mul?.toNat
    for i in range.fst ... (range.snd - 1) do
      let mut ith_num := 0
      for line in lines.take (num_lines - 1) do
        let ch := line[i]!
        if ch.isDigit then
          ith_num := ith_num * 10 + (ch.val - '0'.val).toNat
      if mul? then c := c * ith_num else c := c + ith_num
    total := total + c
  total

end Part2

public def solve := AocProblem.config 2025 06 parser.parse Part1.solve Part2.solve

end Y2025.Day06
