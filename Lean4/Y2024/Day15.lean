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
- empty (default)
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

instance : Inhabited Kind where
  default := .empty

instance : ToString Kind where
  toString s := match s with
    | .empty => " "
    | .wall => "#"
    | .robot => "@"
    | .box => "O"
    | .boxH => "["

#guard s!"{Kind.robot}" == "@"

/-- HashMap based 2D mapping to Kind
- `new (width : Int) : RectHash`
- `[i]? : Option Kind`
- `[i]!`
- `set (i : Vec₂) (k : Kind)`
- `erase (i : Vec₂)`
-/
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

@[inline]
def RectHash.set (self : @&RectHash) (i : Vec₂) (k : Kind) : RectHash :=
  { self with hashmap := self.hashmap.insert (i.fst * self.width + i.snd) k }

@[inline]
def RectHash.erase (self : @&RectHash) (i : Vec₂) : RectHash :=
  { self with hashmap := self.hashmap.erase (i.fst * self.width + i.snd) }

#guard (RectHash.new 10)[(↑ (1,1) : Vec₂)]? == none

/-- The given configuration.
- `mapping : RectHash`
- `moves : Array Dir`
- `pos : Vec₂`
-/
structure Input where
  mapping : RectHash
  moves   : Array Dir
  pos     : Vec₂
deriving BEq

instance : ToString Input where
  toString s := s!"Input: {s.mapping.hashmap.toList} {s.moves}"

namespace Input

def new (ma : Array (Array Kind)) (mv : Array Dir) : Input := Id.run do
  let mut mapping : RectHash := RectHash.new ma[0]!.size
  let mut pos : Vec₂ := default
  for (i, l) in ma.iter.enumerate do
    for (j, k) in l.iter.enumerate do
      if k != .empty && k != .robot then mapping := mapping.set (i, j) k
      if k == Kind.robot then pos := (i, j)
  return Input.mk mapping mv pos

-- def dump (state : Input) : Rect Kind := state.mapping.set state.pos Kind.robot

end Input

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

def parse : String → Option Input := AoCParser.parse (Input.new <$> parseGrid <*> parseMoves)

end parser

namespace Part1

def press (mapping : RectHash) (pos : Vec₂) (dir : Dir) : RectHash × Vec₂ := Id.run do
  let next := pos + dir.asVec₂
  let mut p := next
  while mapping[p]? == some Kind.box do p := p + dir.asVec₂
  match mapping[p]? with
    | none => return (mapping.set p Kind.box |>.erase next, next)
    | _    => return (mapping, pos)

def evaluate (mapping : RectHash) : Nat :=
  mapping.hashmap.iter
    |>.map (fun (i, k) ↦ if k == Kind.box then (i / mapping.width * 100 + i % mapping.width).toNat else 0)
    |>.sum

def solve (input : Input) : Nat := Id.run do
  let mut mapping := input.mapping
  let mut pos := input.pos
  for d in input.moves do (mapping, pos) := press mapping pos d
  return (evaluate mapping)

end Part1

namespace Part2

partial def unsupportedE? (mapping : RectHash) (pos : Vec₂) (half : Bool) : Bool := Id.run do
  let e := pos + Dir.E
  match mapping[pos]?, half with
  | none       , _     => true
  | some .wall , _     => false
  | some .box  , false => unsupportedE? mapping e half
  | some .box  , true  => dbg "ERROR167" false
  | some .boxH , false => true
  | some .boxH , true  => unsupportedE? mapping e half
  | _          , _     => dbg "ERROR170" false

partial def unsupportedW? (mapping : RectHash) (pos : Vec₂) (half : Bool) : Bool := Id.run do
  match mapping[pos]?, half with
  | none        , false
  | some .boxH  , false =>
      -- w might be out of range, so we must define w only if it's really needed.
      let w := pos + Dir.W;  mapping[w]? != some Kind.boxH || unsupportedW? mapping w false
  | none        , true  => true
  | some .wall  , _     => false
  | some .box   , _     => let w := pos + Dir.W; unsupportedW? mapping w true
  | some .boxH  , true  => dbg "ERROR184" false
  | _           , _     => dbg "ERROR185" false

partial def unsupportedS? (mapping : RectHash) (pos : Vec₂) (half : Bool) : Bool := Id.run do
  let s := pos + Dir.S
  match mapping[pos]?, half with
  | some .wall  , _     => false
  | some .box   , _     => unsupportedS? mapping s false && unsupportedS? mapping s true
  | none        , true  => true
  | none        , false
  | some .boxH  , false =>
    let (w, sw) := (pos + Dir.W, s + Dir.W)
    mapping[w]? != some .boxH || (unsupportedS? mapping sw true && unsupportedS? mapping s false)
  | some .boxH  , true  =>
    let se := s + Dir.E;  unsupportedS? mapping s true && unsupportedS? mapping se false
  | _           , _     => dbg "ERROR202" false

partial def unsupportedN? (mapping : RectHash) (pos : Vec₂) (half : Bool) : Bool := Id.run do
  match mapping[pos]?, half with
  | some .wall  , _     => false
  | some .box   , _     =>
    let n := pos + Dir.N; unsupportedN? mapping n false && unsupportedN? mapping n true
  | none        , true  => true
  | none        , false
  | some .boxH  , false =>
    let (n, w, nw) := (pos + Dir.N, pos + Dir.W, pos + Dir.N + Dir.W)
    mapping[w]? != some .boxH || (unsupportedN? mapping nw true && unsupportedN? mapping n false)
  | some .boxH  , true  =>
    let (n, ne) := (pos + Dir.N, pos + Dir.N + Dir.E)
    unsupportedN? mapping n true && unsupportedN? mapping ne false
  | _           , _     => dbg "ERROR222" false

partial def unsupported? (mapping : RectHash) (dir : Dir) (pos: Vec₂) (half : Bool) : Bool := Id.run do
  match dir with
  | .N => unsupportedN? mapping pos half
  | .E => unsupportedE? mapping pos half
  | .S => unsupportedS? mapping pos half
  | .W => unsupportedW? mapping pos half

/- Shift the adjoining boxes to east -/
partial def shiftE (mapping : RectHash) (pos : Vec₂) (half : Bool) : RectHash := Id.run do
  let e := pos + Dir.E
  match mapping[pos]?, half with
  | some .box , false => shiftE mapping e false |>.set pos .boxH
  | some .boxH, true  => shiftE mapping e true |>.erase pos |>.set e .box
  | _         , _     => mapping

partial def shiftW (mapping : RectHash) (pos : Vec₂) (half : Bool) : RectHash := Id.run do
  let w := pos + Dir.W
  match mapping[pos]?, half with
  | none       , false
  | some .boxH , false =>
    if mapping[w]? == some .boxH then shiftW mapping w false |>.set w .box else mapping
  | some .box  , false => shiftW mapping w true |>.erase pos |>.set w .boxH
  | some .box  , true  => shiftW mapping w true |>.erase pos |>.set w .boxH
  | _          , _     => mapping;

partial def shiftS (mapping : RectHash) (pos : Vec₂) (half : Bool) : RectHash := Id.run do
  let s := pos + Dir.S
  match mapping[pos]?, half with
  | none       , false
  | some .boxH , false =>
    let (w, sw) := (pos + Dir.W, s + Dir.W)
    if mapping[w]? == some .boxH then
      mapping |> (shiftS · sw true) |> (shiftS · s false) |>.erase w |>.set sw .boxH
    else
      mapping
  | some .box , false  =>
    mapping |> (shiftS · s false) |> (shiftS · s true) |>.erase pos |>.set s .box
  | some .boxH, true   =>
    mapping |> (shiftS · s true) |> (shiftS · (s + Dir.E) false) |>.erase pos |>.set s .boxH
  | some .box, true    =>
    mapping |> (shiftS · s false) |> (shiftS · s true) |>.erase pos |>.set s .box
  | _        , _       => mapping;

partial def shiftN (mapping : RectHash) (pos : Vec₂) (half : Bool) : RectHash := Id.run do
  let n := pos + Dir.N
  match mapping[pos]?, half with
  | none      , false
  | some .boxH, false =>
    let w := pos + Dir.W
    if mapping[w]? == some .boxH then
      let nw := w + Dir.N
      mapping |> (shiftN · nw true) |> (shiftN · n false) |>.erase w |>.set nw .boxH
    else
      mapping
  | some .box, false  =>
    mapping |> (shiftN · n false) |> (shiftN · n true) |>.erase pos |>.set n .box
  | some .boxH, true  =>
    mapping |> (shiftN · n true) |> (shiftN · (n + Dir.E) false) |>.erase pos |>.set n .boxH
  | some .box, true   =>
    mapping |> (shiftN · n false) |> (shiftN · n true) |>.erase pos |>.set n .box
  | _        , _      => mapping

partial def shift (mapping : RectHash) (dir : Dir) (pos : Vec₂) (half : Bool) : RectHash := Id.run do
  match dir with
  | .N => shiftN mapping pos half
  | .E => shiftE mapping pos half
  | .S => shiftS mapping pos half
  | .W => shiftW mapping pos half

def move (mapping : RectHash) (pos : Vec₂) (half : Bool) (dir : Dir) : RectHash × Vec₂ × Bool := Id.run do
  let (pos', half') := match dir, half with
    | .N, _     => (pos + Dir.N, half)
    | .S, _     => (pos + Dir.S, half)
    | .E, false => (pos, true)
    | .E, true  => (pos + Dir.E, false)
    | .W, false => (pos + Dir.W, true)
    | .W, true  => (pos, false)
  if unsupported? mapping dir pos' half' then
    (shift mapping dir pos' half', pos', half')
  else
    (mapping, pos, half)

def evaluate (mapping : RectHash) : Nat :=
  mapping.hashmap.iter
    |>.map (fun (i, k) ↦ match k with
        | .box  => (i / mapping.width * 100 + i % mapping.width * 2).toNat
        | .boxH => (i / mapping.width * 100 + i % mapping.width * 2 + 1).toNat
        | _     => 0)
    |>.sum

def solve (input : Input) : Nat := Id.run do
  let mut mapping := input.mapping
  let mut pos := input.pos
  let mut halfPos := false
  for d in input.moves do (mapping, pos, halfPos) := move mapping pos halfPos d
  return (evaluate mapping)

end Part2

public def solve := AocProblem.config 2024 15 parser.parse Part1.solve Part2.solve

end Y2024.Day15
