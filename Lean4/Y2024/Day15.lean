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

/-- The status. -/
structure State where
  mapping : Rect Kind
  moves   : Array Dir
  pos     : Idx₂
  posHalf : Bool
deriving BEq, Hashable

namespace Input

def new (ma : Array (Array Kind)) (mv : Array Dir) : State :=
    State.mk (Rect.of2DMatrix ma) mv (default : Idx₂) false

end Input


instance : ToString State where
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

@[inline]
public def parseAs {α : Type} (ch : Char) (a : α) : Parser α := pchar ch *> pure a

infixr:80 " ?> " => parseAs

def parseKind : Parser Kind := do
  ('.' ?> Kind.empty) <|>
  ('#' ?> Kind.wall) <|>
  ('@' ?> Kind.robot) <|>
  ('o' ?> Kind.box) <|>
  ('O' ?> Kind.boxH)

#guard AoCParser.parse parseKind "#" == some Kind.wall

def parseGridLine : Parser (Array Kind) := many1 parseKind <* eol

#guard AoCParser.parse parseGridLine "#.@\n" == some #[Kind.wall, .empty, .robot]

def parseGrid : Parser (Array (Array Kind)) := many1 parseGridLine <* eol

def parseDir : Parser Dir := do
  ('^' ?> Dir.N) <|>
  ('>' ?> Dir.E) <|>
  ('v' ?> Dir.S) <|>
  ('<' ?> Dir.W)

def parseMoves : Parser (Array Dir) := many1 parseDir <* eol

#guard AoCParser.parse parseMoves "^>v\n" == some #[Dir.N, Dir.E, Dir.S]

def parse : String → Option State := AoCParser.parse (Input.new <$> parseGrid <*> parseMoves)

end parser

namespace Part1

def solve (_ : State) : Nat := Id.run do 0

end Part1

namespace Part2

def solve (_ : State) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2024 15 parser.parse Part1.solve Part2.solve

end Y2024.Day15
