import Std
import Lean.Data.Parsec
import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser
import Mathlib.Algebra.Order.WithZero
-- import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Order.LinearOrder

namespace Day10
open Std CiCL CoP

def Pos : Type := Nat × Nat
deriving BEq, Repr, ToString

def Pos.lt (a : Pos) (b : Pos) : Bool := uncurry and <| both2 (fun i j => i < j) a b

def Pos.double : Pos → Pos := both (· * 2)

-- #eval Pos.double ((3, 4) : Pos)
-- #eval Pos.double ((3, 5) : Pos)

def makeNeighbors (size s : Pos) : List Pos :=
  [(s.fst + 1, s.snd + 0), (s.fst - 1, s.snd + 0), (s.fst + 0, s.snd + 1), (s.fst + 0, s.snd - 1)]
    |>.filter (Pos.lt · size)

#eval makeNeighbors (10, 10) (9, 8)

def makeVecs (size start : Pos) : List (Pos × Pos) := makeNeighbors size start |>.map ((start, ·))

-- #eval makeVecs (10, 10) (2, 2)

instance : ToString Pos where
  toString s := s!"P({s.fst}, {s.snd})"

inductive Circuit where
  | v : Circuit
  | h : Circuit
  | l : Circuit
  | j : Circuit
  -- | k : Circuit
  -- | f : Circuit
  | s : Circuit
  | x : Circuit
deriving BEq, Repr

instance : Inhabited Circuit where
  default := Circuit.x

instance : ToString Circuit where
  toString s :=
  match s with
  | .v => "|"
  | .h => "-"
  | .l => "L"
  | .j => "J"
  -- | .k => "7"
  -- | .f => "F"
  | .s => "S"
  | _  => " "

def Circuit.ofChar (c : Char) : Circuit :=
  match c with
  | '|' => .v
  | '-' => .h
  | 'L' => .l
  | 'J' => .j
  | '7' => .l -- .k
  | 'F' => .j -- .f
  | 'S' => .s
  |  _  => .x

-- #eval (Circuit.ofChar 'f') |> toString

def startPosition (self : Mat1 Circuit) : Pos :=
  self.findIdx? (· == Circuit.s) |>.getD (0, 0)

@[inline]
def destinationVector (mat : Mat1 Circuit) (vec : Pos × Pos) : Pos × Pos :=
  let (pre, now) := vec
  let (dy, dx)   := both2 (fun x y => Int.ofNat x - Int.ofNat y) now pre
  let trans      := fun x y => Int.ofNat x + y |>.toNat
  let diff       := match uncurry mat.get? now with
  | some .v => ( dy,   0)
  | some .h => (  0,  dx)
  | some .l => ( dx,  dy) -- | some .k => ( dx,  dy)
  | some .j => (-dx, -dy) -- | some .f => (-dx, -dy)
  |       _ => (  0,   0)
  (now, both2 trans now diff)

def findLoop (mat : Mat1 Circuit) (limit : Nat) (start : Pos) (path : List Pos) (v : Pos × Pos)
    : List Pos :=
  match limit with
  | 0       => []
  | lim + 1 =>
    let v' := destinationVector mat v
    if v'.fst == v'.snd
    then if v'.snd == start then v'.fst :: path else []
    else findLoop mat lim start (v'.fst :: path) v'

namespace parser
open Lean.Parsec AoCParser

def cell := pchar '|'
    <|> pchar '-'
    <|> pchar 'L'
    <|> pchar 'J'
    <|> pchar '7'
    <|> pchar 'F'
    <|> pchar '.'
    <|> pchar 'S'

def pcircuit := (return Circuit.ofChar) <*> cell

def parser := (return Mat1.of2DMatrix) <*>many (many pcircuit <* eol)

end parser

def Part1.solve (m : Mat1 Circuit) : Nat :=
  let st := startPosition m
  makeVecs m.shape st
  |>.map (findLoop m m.size st [st] .)
  |>.map List.length
  |>.maximum?
  |>.getD 0
  |> (· / 2)

structure Map where
  new ::
  size : Pos
  cells : Array Bool

namespace part2
open Lean Data

/-!
  We need a matrix of uncheked, block, open, encoded as none, some true, some false
  1. pick the looping route
  2. double the scale
  3. draw the loop
  4. run propagation
  5. count the unmarked cells
-/

def OBool := Option Bool
deriving BEq, Inhabited

def mappingOf (size : Pos) (locs : List Pos) : Mat1 OBool :=
  let s' := (max 1 size.fst, max 1 size.snd)
  let noneZero : s'.fst * s'.snd > 0 := by simp
  locs.foldl (fun mat pos => mat.set₂ pos (some true)) (Mat1.new! s' noneZero none)

-- #eval mappingOf (2, 2) [(0,0), (1,1)]

def Pos.interpolate (p : Pos) (q : Pos) : Pos :=
  let p' := Pos.double p
  let q' := Pos.double q
  ((p'.fst + q'.fst) / 2, (p'.snd + q'.snd) / 2)

-- #eval Pos.interpolate ((3, 4) : Pos) ((3, 5) : Pos)

/--
This generates a list of dupicated nodes.
-/
def scaleUp : List Pos → List Pos
  | []          => []
  | p :: []     => [Pos.double p]
  | p :: q :: l => [Pos.double p, Pos.interpolate p q] ++ scaleUp (q :: l)

def print (r : Mat1 OBool) : IO Unit := do
  let sp := both (· / 2) r.shape
  let _ ← List.range sp.1
    |>.mapM
      (fun i => do
        let _ ← List.range sp.2
          |>.mapM
            (fun j => do
              match r.get (i * 2) (j * 2) with
              | none       => IO.print "."
              | some false => IO.print "x"
              | some true  => IO.print "#"
            )
        IO.print "\n"
        return ())
  return ()

-- #eval makeNeighbors (10, 10) (0, 0)

-- FIXME: use `foldWithIdx`
partial def propagate (mat : Mat1 OBool) (toVisit : Mat1 Bool) : Mat1 OBool :=
  let (progress, mat', toVisit') := toVisit.foldWithIdx
    (fun curr i j e =>
      match e with
      | false => curr
      | true  =>
        makeNeighbors mat.shape (i, j)
        |>.foldl
          (fun curr@(_, mat, toVisit) next =>
            match mat.get₂ next with
            | some _ => curr
            | none   => (true, mat.set₂ next (some false), toVisit.set₂ next true))
          curr)
    (false, mat, toVisit.cloneWith false)
  if progress then propagate mat' toVisit' else mat'

def solve (m: Mat1 Circuit) : IO Nat := do
  let st := startPosition m
  let sp := m.shape
  let loop := makeVecs sp st
    |>.map (findLoop m m.size st [st] .)
    |>.foldl (fun best cand => if best.length < cand.length then cand else best) []
    |> scaleUp
  let m2 := mappingOf (Pos.double sp) loop
  -- print m2
  -- IO.println s!"{m2.shape}"
  let r := propagate m2 (m2.cloneWith false |>.set 0 0 true)
  -- IO.println ""
  -- print r
  return r.countWithIdx (fun i j e => i % 2 == 0 && j % 2 == 0 && e == none)
  -- let r := mappingOf (Pos.double sp) (dbgTraceVal loop)
  -- (
  --   r.countWithIdx (fun i j e => i % 2 == 0 && j % 2 == 0 && e == none),
  --   r.countWithIdx (fun i j e => i % 2 == 0 && j % 2 == 0 && e == some false),
  --   r.countWithIdx (fun i j e => i % 2 == 0 && j % 2 == 0 && e == some true),
  -- )

-- #eval List.range 9

end part2

end Day10

def day10 (ext : Option String) : IO Answers := do
  if let some (some m) := AoCParser.parse Day10.parser.parser (← dataOf 2023 10 ext)
  then
    return (s!"{Day10.Part1.solve m}", s!"{← Day10.part2.solve m}")
  else return ("parse error", "")
