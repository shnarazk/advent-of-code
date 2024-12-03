import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
-- import «AoC».Rect64

namespace Y2024.Day03

open Accumulation CiCL

inductive Inst
  | Do
  | Dont
  | Mul (vals : Nat × Nat)
deriving BEq, Repr

abbrev Input := Array Inst
instance : ToString Input where toString s := s!"{s.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_mul : Parser Inst := do
  let a ← pstring "mul(" *> (number <* pstring ",")
  let b ← number <* pstring ")"
  return Inst.Mul (a, b)
-- #eval AoCParser.parse parse_pair "mul(3,5)"

def parse_do : Parser Inst := pstring "do()" *> return Inst.Do
#eval AoCParser.parse parse_do "do()o"

def parse_dont : Parser Inst := pstring "don't()" *> return Inst.Dont
#eval AoCParser.parse parse_dont "don't()do"

def parse_inst : Parser Inst := orElse parse_mul (fun _ ↦ orElse parse_do (fun _ ↦ parse_dont))
#eval AoCParser.parse parse_inst "don't()"

def parse_inst' (n : Nat) : Parser Inst := do
  match n with
  | 0 => parse_inst
  | n + 1 => orElse parse_inst (fun _ ↦ any *> (parse_inst' n))
#eval AoCParser.parse (parse_inst' 100) "xxmul(2,5)x"
#eval AoCParser.parse (parse_inst' 100) "xdon't()y"

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser (Array Inst) := endBy (parse_inst' 100) (notFollowedBy (parse_inst' 100))
--    parser : Parser (Array Inst) := many (parse_inst' 100)
#eval AoCParser.parse (many (pstring "ab")) "ababab "
-- #eval AoCParser.parse (many parse_inst') "xxdo()xdo()y"
#eval parse "xxmul(1,2)xdon't()x"

end parser

namespace Part1

def solve (_ : Input) : Nat := 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := 0

end Part2

def solve := AocProblem.config 2024 03
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2024.Day03
