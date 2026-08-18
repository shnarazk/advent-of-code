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

/-- Category of items in the map:
- empty
- wall
- robot
- box
- boxH, used in part2
-/
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
- pos : `Idx₂`
- posHalf : `Bool`
-/
structure State where
  mapping : Rect Kind
  moves   : Array Dir
  pos     : Idx₂
  posHalf : Bool
deriving BEq, Hashable

instance : ToString State where
  toString s := s!"State: {s.mapping} {s.moves}"

namespace State

def new (ma : Array (Array Kind)) (mv : Array Dir) : State :=
  let mapping : Rect Kind := Rect.of2DMatrix ma
  match mapping.findPosition? (· == Kind.robot) with
  | some p => State.mk (mapping.set p Kind.empty) mv p false
  | none => State.mk mapping mv default false

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

infixr:90 " ?> " => parseAs

def parseKind : Parser Kind := do
  '.' ?> Kind.empty <|>
  '#' ?> Kind.wall <|>
  '@' ?> Kind.robot <|>
  'O' ?> Kind.box

#guard AoCParser.parse parseKind "#" == some Kind.wall

def parseGridLine : Parser (Array Kind) := many1 parseKind <* eol

#guard AoCParser.parse parseGridLine "#.@\n" == some #[Kind.wall, .empty, .robot]

def parseGrid : Parser (Array (Array Kind)) := many1 parseGridLine <* eol

def parseDir : Parser Dir := do
  '^' ?> Dir.N <|>
  '>' ?> Dir.E <|>
  'v' ?> Dir.S <|>
  '<' ?> Dir.W

def parseMoves : Parser (Array Dir) := Array.flatten <$> (many1 (many1 parseDir <* eol))

#guard AoCParser.parse parseMoves "^>v<\n" == some #[Dir.N, .E, .S, .W]

def parse : String → Option State := AoCParser.parse (State.new <$> parseGrid <*> parseMoves)

end parser

namespace Part1

def press (state : State) : State := Id.run do
  let some dir := state.moves[0]? | return state
  let moves := state.moves.drop 1
  let some next := toIdx₂ ((↑ state.pos : Vec₂) + dir.asVec₂) | return dbg "ERROR" state
  let mut p := next
  while state.mapping.get? p == some Kind.box do
    -- let some q := toIdx₂ ((↑ p : Vec₂) + dir.asVec₂) | return dbg "ERROR" state
    let q := toIdx₂ ((↑ p : Vec₂) + dir.asVec₂)
    if q.isNone then return dbg "error" state
    p := q.unwrapOr next
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
    |>.map (fun (p, k) ↦ if k == Kind.box then p.fst * 100 + p.snd else 0)
    |>.sum

def solve (state : State) : Nat := Id.run do
  let mut s := state
  while ! s.moves.isEmpty do s := press s
  return (evaluate s)

end Part1

namespace Part2

partial def _root_.Y2024.Day15.State.move (s : State) : State := s

partial def unsupportedE (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  let some e := pos + Dir.E | panic "ERROR"
  match state.mapping.get? pos, half with
  | some Kind.empty , _     => true
  | some Kind.wall  , _     => false
  | some Kind.box   , false => unsupportedE state e half
  | some Kind.box   , true  => panic "ERROR"
  | some Kind.boxH  , false => true
  | some Kind.boxH  , true  => unsupportedE state e half
  | _               , _     => panic "ERROR"

partial def unsupportedW (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  let some w := pos + Dir.W | panic "ERROR"
  match state.mapping.get? pos, half with
  | some Kind.empty , false => state.mapping.get w Kind.boxH != Kind.boxH || unsupportedW state w false
  | some Kind.empty , true  => true
  | some Kind.wall  , _     => false
  | some Kind.box   , false => unsupportedW state w true
  | some Kind.box   , true  => unsupportedW state w half
  | some Kind.boxH  , false => state.mapping.get w Kind.boxH != Kind.boxH || unsupportedW state w false
  | some Kind.boxH  , true  => panic "ERROR"
  | _               , _     => panic "ERROR"

partial def unsupportedS (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  let some s := pos + Dir.S | panic "ERROR"
  match state.mapping.get? pos, half with
  | some Kind.empty , false =>
    let some w := pos + Dir.W | panic "ERROR";
    let some sw := w + Dir.S  | panic "ERROR";
    state.mapping.get w Kind.boxH != Kind.boxH
    || (unsupportedS state sw true && unsupportedS state s true)
  | some Kind.empty , true  => true
  | some Kind.wall  , _     => false
  | some Kind.box   , _     => unsupportedS state s false && unsupportedS state s true
  | some Kind.boxH  , false =>
    let some w := pos + Dir.W | panic "ERROR";
    let some sw := w + Dir.S  | panic "ERROR";
    state.mapping.get w Kind.boxH != Kind.boxH
    || (unsupportedS state sw true && unsupportedS state s true)
  | _               , _     => panic "ERROR"

partial def unsupportedN (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  let some n := pos + Dir.N | panic "ERROR"
  match state.mapping.get? n, half with
  | some Kind.empty , false =>
    let some w := pos + Dir.W | panic "ERROR";
    let some nw := w + Dir.N  | panic "ERROR";
    state.mapping.get w Kind.boxH != Kind.boxH ||
    (unsupportedN state nw true && unsupportedN state n false)
  | some Kind.empty , true  => true
  | some Kind.wall  , _     => false
  | some Kind.box   , _     => unsupportedN state n false && unsupportedN state n true
  | some Kind.boxH  , false =>
    let some w := pos + Dir.W | panic "ERROR";
    let some nw := w + Dir.N  | panic "ERROR";
    state.mapping.get w Kind.boxH != Kind.boxH ||
    (unsupportedN state nw true && unsupportedN state n false)
  | some Kind.boxH  , true  =>
    let some e := pos + Dir.E | panic "ERROR";
    let some ne := e + Dir.N  | panic "ERROR";
    unsupportedN state n true && unsupportedN state ne false
  | _               , _     => panic "ERROR"

partial def unsupported (state : State) (dir : Dir) (pos: Idx₂) (half : Bool) : Bool := Id.run do
  match dir with
  | .N => unsupportedN state pos half
  | .E => unsupportedE state pos half
  | .S => unsupportedS state pos half
  | .W => unsupportedW state pos half

/- Shift the adjoining boxes to east -/
partial def shiftE (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some e := pos + Dir.E | return dbg "ERROR" state;
  match state.mapping.get? pos, half with
  | some Kind.empty, _   => return state
  | some Kind.box, false =>
    let s' := shiftE state e half
    return { s' with mapping := state.mapping.set pos Kind.boxH }
  | some Kind.box, true  =>
    let s' := shiftE state e half
    return { s' with mapping := state.mapping.set pos Kind.boxH |>.set e Kind.box }
  | _, _ => return state

partial def shiftW (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some w := pos + Dir.W | return dbg "ERROR" state;
  match state.mapping.get? pos, half with
  | some Kind.empty, false | some Kind.boxH, false =>
    if state.mapping.get w Kind.empty == Kind.boxH then
      let s' := shiftW state w false
      return { s' with mapping := state.mapping.set w Kind.box }
    else
      return state
  | some Kind.box, false =>
    let s' := shiftW state w true
    return { s' with mapping := state.mapping.set pos Kind.empty |>.set w Kind.boxH }
  | some Kind.box, true  =>
    let s' := shiftW state w half
    return { s' with mapping := state.mapping.set pos Kind.empty |>.set w Kind.boxH }
  | _, _ => return state

partial def shiftS (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some s := pos + Dir.S | return dbg "ERROR" state;
  match state.mapping.get? pos, half with
  | some Kind.empty, false | some Kind.boxH, false =>
    let some w := pos + Dir.W | return dbg "ERROR" state;
    let some sw := w + Dir.S | return dbg "ERROR" state;
    if state.mapping.get w Kind.empty == Kind.boxH then
      let mut s' := shiftS state sw true
      s' := shiftS s' s false
      return { s' with mapping := state.mapping.set w Kind.empty |>.set sw Kind.boxH }
    else
      return state
  | some Kind.box, false =>
    let mut s' := shiftS state s false
    s' := shiftS s' s true
    return { s' with mapping := state.mapping.set pos Kind.empty |>.set s Kind.box }
  | some Kind.empty, true => return state
  | some Kind.boxH, true =>
    let some se := s + Dir.E | return dbg "ERROR" state;
    let mut s' := shiftS state s true
    s' := shiftS s' se false
    return { s' with mapping := state.mapping.set pos Kind.empty |>.set s Kind.boxH }
  | some Kind.box, true =>
    let mut s' := shiftS state s false
    s' := shiftS s' s true
    return { s' with mapping := state.mapping.set pos Kind.empty |>.set s Kind.box }
  | _, _ => dbg "ERROR" state

partial def shiftN (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some n := pos + Dir.N | return dbg "ERROR" state;
  match state.mapping.get? pos, half with
  | some Kind.empty, false | some Kind.boxH, false =>
    let some w := pos + Dir.W | return dbg "ERROR" state;
    let some nw := w + Dir.N | return dbg "ERROR" state;
    if state.mapping.get? w == some Kind.boxH then
      let mut s' := shiftN state nw true
      s' := shiftN s' n false
      return { s' with mapping := state.mapping.set w Kind.empty |>.set nw Kind.boxH }
    else
      state
  | some Kind.box, false =>
      let mut s' := shiftN state n false
      s' := shiftN s' n true
      return { s' with mapping := state.mapping.set pos Kind.empty |>.set n Kind.box }
  | some Kind.empty, true => return state
  | some Kind.boxH, true =>
    let some ne := n + Dir.E | return dbg "ERROR" state;
    let s' := state |> (shiftN · n true) |> (shiftN · ne false)
    return { s' with mapping := state.mapping.set pos Kind.empty |>.set n Kind.boxH }
  | some Kind.box, true =>
    let s' := state |> (shiftN · n true) |> (shiftN · n false)
    return { s' with mapping := state.mapping.set pos Kind.empty |>.set n Kind.box }
  | _, _ => state

partial def shift (state : State) (dir : Dir) (pos : Idx₂) (half : Bool) : State := Id.run do
  match dir with
  | .N => shiftN state pos half
  | .E => shiftE state pos half
  | .S => shiftS state pos half
  | .W => shiftW state pos half

partial def move (state : State) : State := Id.run do
  let some dir := state.moves[0]? | return state;
  let moves := state.moves.drop 1
  let next := match dir, state.posHalf with
    | Dir.N, b     => (state.pos + Dir.N, b)
    | Dir.S, b     => (state.pos + Dir.S, b)
    | Dir.E, false => (state.pos, true)
    | Dir.E, true  => (state.pos + Dir.E, false)
    | Dir.W, false => (state.pos + Dir.W, true)
    | Dir.W, true  => (state.pos, false)
  if let some p := next.1 then
    if unsupported state dir p next.2 then
      let s := shift state dir p next.2
      return { s with pos := p, moves := moves, posHalf := next.2 }
    else
      return { state with moves := moves }
  else
    return state

def evaluate (state : State) : Nat :=
  state.mapping.enum
  |>.map (fun (pos, kind) => match kind with
     | Kind.box  => pos.fst * 100 + pos.snd
     | Kind.boxH => pos.fst * 100 + pos.snd + 1
     | _         => 0 )
  |>.sum

def solve (state : State) : Nat := Id.run do
  let mut s := state
  while ! s.moves.isEmpty do s := move s
  return evaluate s

end Part2

public def solve := AocProblem.config 2024 15 parser.parse Part1.solve Part2.solve

end Y2024.Day15
