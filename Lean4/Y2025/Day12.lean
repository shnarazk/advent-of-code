module

public import Itertools
public import WinnowParsers
public import «AoC».Basic

namespace Y2025.Day12

structure Input where
  blocks : Array (Array (Array Bool))
  spec : Array ((Nat × Nat) × Array Nat)
deriving BEq, Repr

instance : ToString Input where toString s := s!"{s.blocks.size}, {s.spec.size}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_block := do
  let _id ← number <* pstring ":\n"
  separated (repeated ((· == '#') <$> (pchar '.' <|> pchar '#'))) eol <* eol

-- #eval AoCParser.parse (separated parse_block eol) "4:\n.#\n\n2:\n#..\n"

def parse_setting := do
  let width ← number <* pchar 'x'
  let height ← number <* pstring ": "
  let requirement ← separated number whitespaces
  pure ((width, height), requirement)

-- #eval AoCParser.parse parse_setting "4x4: 0 1 2"

def parse : String → Option Input := AoCParser.parse parser
  where
    parser : Parser Input := Input.mk <$> separated parse_block eol <* eol <*> separated parse_setting eol

end parser

namespace Part1

def solve (input : Input) : Nat := Id.run do
  input.spec.iter
    |>.filter (fun ((width, height), requirement) ↦ width * height ≥ requirement.iter.sum * 9)
    |>.length

end Part1

namespace Part2

def solve (_ : Input) : String := "Y2025 was completed!"

end Part2

public def solve := AocProblem.config 2025 12 parser.parse Part1.solve Part2.solve

end Y2025.Day12
