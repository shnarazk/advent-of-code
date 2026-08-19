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
i void (default)
- empty
- wall
- robot
- box
- boxH, used in part2
-/
inductive Kind where
  | void
  | empty
  | wall
  | robot
  | box
  | boxH
  deriving BEq, Hashable, Repr

instance : Inhabited Kind where
  default := .void

instance : ToString Kind where
  toString s := match s with
    | .void => panic " "
    | .empty => " "
    | .wall => "#"
    | .robot => "@"
    | .box => "O"
    | .boxH => "["

#guard s!"{Kind.robot}" == "@"

structure RectHash where
  hashmap :Std.HashMap Int Kind
  width: Int
deriving BEq, Repr

def RectHash.new (w : Int) : RectHash :=
  RectHash.mk Std.HashMap.emptyWithCapacity w

instance RectHash.isGetElem :
    GetElem? RectHash Vec₂ Kind (fun h i ↦ i.fst * h.width + i.snd ∈ h.hashmap) where
  getElem? self i := self.hashmap[i.fst * self.width + i.snd]?
  getElem self i p := self.hashmap.get (i.fst * self.width + i.snd) p

def RectHash.set (self : @&RectHash) (i : Vec₂) (k : Kind) : RectHash :=
  { self with hashmap := self.hashmap.insert (i.fst * self.width + i.snd) k }

#guard (RectHash.new 10)[(↑ (1,1) : Vec₂)]? == none

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

partial def unsupportedE (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  let some e := pos + Dir.E | return dbg "ERROR162" false
  match state.mapping.get? pos, half with
  | some .empty , _     => true
  | some .wall  , _     => false
  | some .box   , false => unsupportedE state e half
  | some .box   , true  => dbg "ERROR167" false
  | some .boxH  , false => true
  | some .boxH  , true  => unsupportedE state e half
  | _           , _     => dbg "ERROR170" false

partial def unsupportedW (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  match state.mapping.get? pos, half with
  | some .empty , false
  | some .boxH  , false =>
      -- w might be out of range, so we must define w only if it's really needed.
      let some w := pos + Dir.W | return dbg s!"ERROR177({pos})" false
      state.mapping.get? w != some Kind.boxH || unsupportedW state w false
  | some .empty , true  => true
  | some .wall  , _     => false
  | some .box   , _     =>
    let some w := pos + Dir.W | return dbg s!"ERROR182({pos})" false
    unsupportedW state w true
  | some .boxH  , true  => dbg "ERROR184" false
  | _           , _     => dbg "ERROR185" false

partial def unsupportedS (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  let some s := pos + Dir.S | return dbg "ERROR187" false
  match state.mapping.get? pos, half with
  | some .wall  , _     => false
  | some .box   , _     => unsupportedS state s false && unsupportedS state s true
  | some .empty , true  => true
  | some .empty , false
  | some .boxH  , false =>
    let some w := pos + Dir.W | return dbg "ERROR195" false;
    let some sw := w + Dir.S  | return dbg "ERROR196" false;
    state.mapping.get? w != some .boxH
    || (unsupportedS state sw true && unsupportedS state s false)
  | some .boxH  , true  =>
    let some se := s + Dir.E  | return dbg "ERROR200" false;
    unsupportedS state s true && unsupportedS state se false
  | _           , _     => dbg "ERROR202" false

partial def unsupportedN (state: State) (pos : Idx₂) (half : Bool) : Bool := Id.run do
  match state.mapping.get? pos, half with
  | some .wall  , _     => false
  | some .box   , _     =>
    let some n := pos + Dir.N | return dbg "ERROR208" false;
    unsupportedN state n false && unsupportedN state n true
  | some .empty , true  => true
  | some .empty , false
  | some .boxH  , false =>
    let some n := pos + Dir.N | return dbg "ERROR213" false;
    let some w := pos + Dir.W | return dbg "ERROR214" false;
    let some nw := w + Dir.N | return dbg "ERROR215" false;
    state.mapping.get? w != some .boxH ||
      (unsupportedN state nw true && unsupportedN state n false)
  | some .boxH  , true  =>
    let some n := pos + Dir.N | return dbg "ERROR219" false;
    let some ne := n + Dir.E | return dbg "ERROR220" false;
    unsupportedN state n true && unsupportedN state ne false
  | _           , _     => dbg "ERROR222" false

partial def unsupported (state : State) (dir : Dir) (pos: Idx₂) (half : Bool) : Bool := Id.run do
  match dir with
  | .N => unsupportedN state pos half
  | .E => unsupportedE state pos half
  | .S => unsupportedS state pos half
  | .W => unsupportedW state pos half

/- Shift the adjoining boxes to east -/
partial def shiftE (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some e := pos + Dir.E | return dbg "ERROR233" state;
  match state.mapping.get? pos, half with
  | some .box , false =>
    let s' := shiftE state e false
    { s' with mapping := s'.mapping.set pos .boxH }
  | some .boxH, true  =>
    let s' := shiftE state e true
    { s' with mapping := s'.mapping.set pos .empty |>.set e .box }
  | _         , _     => state

partial def shiftW (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some w := pos + Dir.W | return dbg "ERROR244" state;
  match state.mapping.get? pos, half with
  | some .empty, false
  | some .boxH , false =>
    if state.mapping.get? w == some .boxH then
      let s' := shiftW state w false
      { s' with mapping := s'.mapping.set w .box }
    else
      state
  | some .box  , false =>
    let s' := shiftW state w true
    { s' with mapping := s'.mapping.set pos .empty |>.set w .boxH }
  | some .box  , true  =>
    let s' := shiftW state w true
    { s' with mapping := s'.mapping.set pos .empty |>.set w .boxH }
  | _          , _     => state;

partial def shiftS (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some s := pos + Dir.S | return dbg "ERROR262" state;
  match state.mapping.get? pos, half with
  | some .empty, false
  | some .boxH , false =>
    let some w := pos + Dir.W | return dbg "ERROR266" state;
    let some sw := s + Dir.W | return dbg "ERROR267" state;
    if state.mapping.get? w == some .boxH then
      let s' := state |> (shiftS · sw true) |> (shiftS · s false)
      { s' with mapping := s'.mapping.set w .empty |>.set sw .boxH }
    else
      state
  | some .box , false  =>
    let s' := state |> (shiftS · s false) |> (shiftS · s true)
    { s' with mapping := s'.mapping.set pos .empty |>.set s .box }
  | some .boxH, true   =>
    let some se := s + Dir.E | return dbg "ERROR" state;
    let s' := state |> (shiftS · s true) |> (shiftS · se false)
    { s' with mapping := s'.mapping.set pos .empty |>.set s .boxH }
  | some .box, true    =>
    let s' := state |> (shiftS · s false) |> (shiftS · s true)
    { s' with mapping := s'.mapping.set pos .empty |>.set s .box }
  | _        , _       => state;

partial def shiftN (state : State) (pos : Idx₂) (half : Bool) : State := Id.run do
  let some n := pos + Dir.N | return dbg "ERROR286" state;
  match state.mapping.get? pos, half with
  | some .empty, false | some .boxH, false =>
    let some w := pos + Dir.W | return dbg "ERROR289" state;
    if state.mapping.get? w == some .boxH then
      let some nw := w + Dir.N | return dbg "ERROR291" state;
      let s' := state |> (shiftN · nw true) |> (shiftN · n false)
      { s' with mapping := s'.mapping.set w .empty |>.set nw .boxH }
    else
      state
  | some .box, false =>
      let s' := state |> (shiftN · n false) |> (shiftN · n true)
      { s' with mapping := s'.mapping.set pos .empty |>.set n .box }
  | some .boxH, true =>
    let some ne := n + Dir.E | return dbg "ERROR299" state;
    let s' := state |> (shiftN · n true) |> (shiftN · ne false)
    { s' with mapping := s'.mapping.set pos .empty |>.set n .boxH }
  | some .box, true =>
    let s' := state |> (shiftN · n false) |> (shiftN · n true)
    { s' with mapping := s'.mapping.set pos .empty |>.set n .box }
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
  let (next, half) := match dir, state.posHalf with
    | .N, b     => (state.pos + Dir.N, b)
    | .S, b     => (state.pos + Dir.S, b)
    | .E, false => (some state.pos, true)
    | .E, true  => (state.pos + Dir.E, false)
    | .W, false => (state.pos + Dir.W, true)
    | .W, true  => (some state.pos, false)
  if let some p := next then
    if unsupported state dir p half then
      let s := shift state dir p half
      return { s with pos := p, moves := moves, posHalf := half }
    else
      return { state with moves := moves }
  else
    return { state with moves := moves }

def evaluate (state : State) : Nat :=
  state.mapping.enum
  |>.map (fun (pos, kind) => match kind with
     | .box  => pos.fst * 100 + pos.snd * 2
     | .boxH => pos.fst * 100 + pos.snd * 2 + 1
     | _         => 0 )
  |>.sum

def solve (state : State) : Nat := Id.run do
  let mut s := state
  while ! s.moves.isEmpty do s := move s
  return evaluate s

end Part2

public def solve := AocProblem.config 2024 15 parser.parse Part1.solve Part2.solve

end Y2024.Day15
