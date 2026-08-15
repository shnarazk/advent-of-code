module

public import Itertools
public meta import Itertools
public import WinnowParsers
public meta import WinnowParsers
public import «AoC».Basic
public meta import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec
public meta import «AoC».Vec

namespace Y2024.Day15

open Std
open Dim2

inductive Kind where
  | empty
  | wall
  | robot
  | box
  | boxH
  deriving BEq, Hashable, Repr

instance : ToString Kind where
  toString s := match s with
    | .empty => " "
    | .wall => "#"
    | .robot => "@"
    | .box => "o"
    | .boxH => "O"

#guard s!"{Kind.robot}" == "@"

/-- The input data. -/
structure Input where
  mapping : Array (Array Kind)
  moves : Array Dir
deriving BEq, Hashable, Repr

instance : ToString Input where
  toString s := s!"{s.mapping} {s.moves}"

namespace parser

/- Input data format
```
########
#..O.O.#
##@.O..#
#...O..#
#.#.O..#
#...O..#
#......#
########

<^^>>>vv<v>>v<<
```
-/

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseKind : Parser Kind := do
  (pchar '.' *> pure Kind.empty) <|>
  (pchar '#' *> pure Kind.wall) <|>
  (pchar '@' *> pure Kind.robot) <|>
  (pchar 'o' *> pure Kind.box) <|>
  (pchar 'O' *> pure Kind.boxH)

#guard AoCParser.parse parseKind "#" == some Kind.wall

def parseGridLine : Parser (Array Kind) := many1 parseKind <* eol

#guard AoCParser.parse parseGridLine "#.@\n" == some #[Kind.wall, .empty, .robot]

def parseGrid : Parser (Array (Array Kind)) := many1 parseGridLine <* eol

def parseDir : Parser Dir := do
  (pchar '^' *> pure Dir.N) <|>
  (pchar '>' *> pure Dir.E) <|>
  (pchar 'v' *> pure Dir.S) <|>
  (pchar '<' *> pure Dir.W)

def parseMoves : Parser (Array Dir) := many1 parseDir <* eol

#guard AoCParser.parse parseMoves "^>v\n" == some #[Dir.N, Dir.E, Dir.S]

def parse : String → Option Input := AoCParser.parse (Input.mk <$> parseGrid <*> parseMoves)

end parser

namespace Part1

def solve (_ : Input) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : Input) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2024 15 parser.parse Part1.solve Part2.solve

end Y2024.Day15
