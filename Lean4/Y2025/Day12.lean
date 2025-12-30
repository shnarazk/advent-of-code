module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser

namespace Y2025.Day12

structure Input where
  blocks : Array (Array (Array Bool))
  spec : Array ((Nat × Nat) × Array Nat)
deriving BEq, Repr

instance : ToString Input where toString s := s!"{s.blocks.size}, {s.spec.size}"

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parse_block := do
  let _id ← number <* pstring ":\n"
  let shape ← separated (repeated ((· == '#') <$> (pchar '.' <|> pchar '#'))) eol <* eol
  pure shape

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

def solve (_ : Input) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2025 12 parser.parse Part1.solve Part2.solve

end Y2025.Day12
