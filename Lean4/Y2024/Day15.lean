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
    | .box => "O"
    | .boxH => "|"

#guard s!"{Kind.robot}" == "@"

/-- The status.
- mapping : `Rect Kind`
- moves : `Array Dir`
-- - dir : `Dir`
- pos : `Idx₂`
- posHalf : `Bool`
-/
structure State where
  mapping : Rect Kind
  moves   : Array Dir
  -- dir     : Dir
  pos     : Idx₂
  posHalf : Bool
deriving BEq, Hashable

instance : ToString State where
  toString s := s!"{s.mapping} {s.moves}"

namespace State

def new (ma : Array (Array Kind)) (mv : Array Dir) : State :=
  let mapping : Rect Kind := Rect.of2DMatrix ma
  let pos := mapping.findPosition? (· == Kind.robot) |>.unwrapOr (dbg "error" (default : Idx₂))
  State.mk (mapping.set pos Kind.empty) mv pos false

def dump (state : State) : Rect Kind := state.mapping.set state.pos Kind.robot

end State

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

/-- Convert a character to an inductive type. -/
@[inline]
public def parseAs {α : Type} (ch : Char) (a : α) : Parser α := pchar ch *> pure a

infixr:80 " ?> " => parseAs

def parseKind : Parser Kind := do
  ('.' ?> Kind.empty) <|>
  ('#' ?> Kind.wall) <|>
  ('@' ?> Kind.robot) <|>
  ('O' ?> Kind.box)

#guard AoCParser.parse parseKind "#" == some Kind.wall

def parseGridLine : Parser (Array Kind) := many1 parseKind <* eol

#guard AoCParser.parse parseGridLine "#.@\n" == some #[Kind.wall, .empty, .robot]

def parseGrid : Parser (Array (Array Kind)) := many1 parseGridLine <* eol

def parseDir : Parser Dir := do
  ('^' ?> Dir.N) <|>
  ('>' ?> Dir.E) <|>
  ('v' ?> Dir.S) <|>
  ('<' ?> Dir.W)

def parseMoves : Parser (Array Dir) := Array.flatten <$> (many1 (many1 parseDir <* eol))

#guard AoCParser.parse parseMoves "^>v<\n" == some #[Dir.N, .E, .S, .W]

def parse : String → Option State := AoCParser.parse (State.new <$> parseGrid <*> parseMoves)

end parser

namespace Part1

def press (state : State) : State := Id.run do
  let some dir :=  state.moves[0]? | return state
  let moves := state.moves.drop 1
  let some next := toIdx₂ ((↑ state.pos : Vec₂) + dir.asVec₂) | return dbg "error" state
  let mut p := next
  while state.mapping.get? p == some Kind.box do
    let some q := toIdx₂ ((↑ p : Vec₂) + dir.asVec₂) | return dbg "error" state
    p := q
  match state.mapping.get? p with
    | some .empty =>
      return { state with
        mapping := state.mapping.set p Kind.box |>.set next Kind.empty
        moves := moves
        pos := next }
    | some .wall => return { state with moves := moves }
    | _ => return { state with moves := moves }

def evaluate (state : State) : Nat :=
  state.mapping.enum
    |>.map (fun e ↦ let (p, k) := e ; if k == Kind.box then p.fst * 100 + p.snd else 0)
    |>.sum

def solve (state : State) : Nat := Id.run do
  let mut s := state
  while ! s.moves.isEmpty do s := press s
  return (evaluate s)

end Part1

namespace Part2

def solve (_ : State) : Nat := Id.run do 0

end Part2

public def solve := AocProblem.config 2024 15 parser.parse Part1.solve Part2.solve

end Y2024.Day15
