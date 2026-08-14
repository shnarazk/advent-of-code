module

public import Itertools
public import WinnowParsers
public meta import WinnowParsers
public import «AoC».Basic
public meta import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Vec

namespace Y2024.Day14

open Std
open Dim2

/-- The input data.
- We use axis ordering: y -> x. -/
structure Input where
  pos : Vec₂
  vec : Vec₂
deriving BEq, Hashable, Repr

instance : ToString Input where
  toString s := s!"{s.pos}:{s.vec}"

namespace parser

open WinnowParsers
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def parseInput : Parser Input := do
  let p1 ← pstring "p=" *> number_signed
  let p2 ← pstring "," *> number_signed
  let v1 ← pstring " v=" *> number_signed
  let v2 ← pstring "," *> number_signed
  pure <| Input.mk (p2, p1) (v2, v1)

#guard AoCParser.parse parseInput "p=0,4 v=3,-1" == some (Input.mk (4, 0) (-1, 3))

def parse : String → Option (Array Input) := AoCParser.parse parser
  where
    parser : Parser (Array Input) := separated parseInput eol

end parser

namespace Part1

def solve (input : Array Input) : Nat := Id.run do
  let size := if input.size == 12 then (7, 11) else (103, 101)
  let t : Int := 100
  let (hy, hx) := CoP.both (· / 2) size
  let ret : Array Int := input.iter
    |>.map (fun i ↦
      let (pi, pj) := i.pos
      let (si, sj) := i.vec
      let a := (((t * si + pi) % size.1) + size.1) % size.1
      let b := (((t * sj + pj) % size.2) + size.2) % size.2
      match compare a hy, compare b hx with
        | .eq, _ | _, .eq => #[0, 0, 0, 0]
        | .lt, .lt => #[1, 0, 0, 0]
        | .lt, .gt => #[0, 1, 0, 0]
        | .gt, .lt => #[0, 0, 1, 0]
        | .gt, .gt => #[0, 0, 0, 1] )
    |>.fold (Array.zip · · |>.map (CoP.join (· + ·))) #[0, 0, 0, 0]
  return ret.iter.map (·.toNat) |>.product

end Part1

namespace Part2

def solve (input : Array Input) : Nat := Id.run do
  let size := if input.size == 12 then (7, 11) else (103, 101)
  let decay_rate : Float := 0.9
  let num_points : Nat := input.size
  let mut signal_rate : Float := 1.0
  for t in 1 ... 100_000 do
    let t' : Int := Int.ofNat t
    let res : HashSet Vec₂ := input
      |>.iter
      |>.map (fun p ↦
        let (pi, pj) := p.pos
        let (si, sj) := p.vec
        ( (((t' * si + pi) % size.1) + size.1) % size.1,
          (((t' * sj + pj) % size.2) + size.2) % size.2) )
      |>.toHashSet'
    let num_connected := res
      |>.iter
      |>.filter (fun a ↦ #[Dir.N, .E, .S, .W].iter.map (a + ·) |>.any (res.contains ·))
      |>.length
    let r := num_connected.toFloat / num_points.toFloat
    if r / signal_rate > 4.0 then return t
    signal_rate := signal_rate * decay_rate
    signal_rate := signal_rate + (1.0 - decay_rate) * r
  return 0


end Part2

public def solve := AocProblem.config 2024 14 parser.parse Part1.solve Part2.solve

end Y2024.Day14
