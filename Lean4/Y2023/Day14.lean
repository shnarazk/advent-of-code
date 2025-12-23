module

public import «AoC».Basic
public import «AoC».Combinator
public import «AoC».Parser
public import «AoC».Vec

open Accumulation CiCL BQN
open Dim2

inductive Kind where
  | Round : Kind
  | Cube  : Kind
  | Empty : Kind
deriving BEq, Repr, Hashable

instance : Inhabited Kind where default := .Empty

instance : ToString Kind where
  toString : Kind → String
    | Kind.Round => "O"
    | Kind.Cube  => "#"
    | Kind.Empty => "."

instance : ToString Dir where
  toString s :=
    match s with
      | .N => "N"
      | .E => "E"
      | .S => "S"
      | .W => "W"

-- #eval Dir.N.rotate.rotate.rotate.rotate

namespace Dim2.Rect

-- notation:50 lhs " _ " rhs => Dim2.mk lhs rhs
-- #eval 30 _ 40

def pullUp (self : Rect Kind) (dir : Dir) : Rect Kind :=
  let height : Nat := self.vector.size / self.width
  let width : Nat := self.width
  match dir with
  | .N =>
    (List.range width).foldl
      (fun m x ↦
        (List.range height).foldl
          (fun (m, empty) y ↦
            match m.get (y, x) Kind.Empty with
            | Kind.Round => (m.swap (empty, x) (y, x), empty + 1)
            | Kind.Cube  => (m, y + 1)
            | Kind.Empty => (m, empty))
          (m, 0)
        |>.fst)
      self
   | .S =>
    (List.range width).foldl
        (fun m x ↦
          (List.range height|>.reverse).foldl
            (fun (m, empty) y ↦
              match m.get (y, x) Kind.Empty with
              | Kind.Round => (m.swap (empty, x) (y, x), empty - 1)
              | Kind.Cube  => (m, y - 1)
              | Kind.Empty => (m, empty))
            (m, self.width - 1)
          |>.fst)
        self
    | .E =>
      (List.range height).foldl
        (fun m y ↦
          (List.range width |>.reverse).foldl
            (fun (m, empty) x ↦
              match m.get (y, x) Kind.Empty with
              | Kind.Round => (m.swap (y, empty) (y, x), empty - 1)
              | Kind.Cube  => (m, x - 1)
              | Kind.Empty => (m, empty))
            (m, self.width - 1)
          |>.fst)
        self
    | .W =>
      (List.range height).foldl
        (fun m y ↦
          (List.range width).foldl
            (fun (m, empty) x ↦
              match m.get (y, x) Kind.Empty with
              | Kind.Round => (m.swap (y, empty) (y, x), empty + 1)
              | Kind.Cube  => (m, x + 1)
              | Kind.Empty => (m, empty))
            (m, 0)
          |>.fst)
        self

def spin : Rect Kind → Rect Kind := [.N, .W, .S, .E].foldl (·.pullUp ·)
-- #eval [Dir.N, .W, .S, .E].foldl (fun acc x ↦ s!"{acc} => {x}") ""

def evaluate (self : Rect Kind) : Nat :=
  let height : Nat := self.vector.size / self.width
  (List.range height).foldl
    (fun c y ↦
      (List.range self.width).foldl
        (fun c x ↦
          match self.get (y, x) Kind.Empty with
          | Kind.Round => c + height - y
          | Kind.Cube  => c
          | Kind.Empty => c)
        c)
    (0 : Nat)

end Dim2.Rect

namespace Y2023.Day14

namespace parser

open AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def cell := pchar 'O' <|> pchar '#' <|> pchar '.'

def maze_line := do
  let v ← many1 cell <* eol
  return  v.map (match · with | 'O' => Kind.Round | '#' => Kind.Cube | _ => Kind.Empty)

def maze := many1 maze_line >>= pure ∘ Rect.of2DMatrix

def parse : String → Option (Array (Rect Kind)) := AoCParser.parse parser
  where
    parser := separated maze eol

end parser

namespace Part1

def solve (as: Array (Rect Kind)) : Nat := as.map (·.pullUp Dir.N |>.evaluate) |>sum

end Part1

namespace Part2

open Std.HashMap

private def loopTo' (self : Rect Kind) (n : Nat) (memory : Std.HashMap (Rect Kind) Int) (i : Nat)
    : Rect Kind :=
  if n ≤ i then
    self
  else
    let next : Rect Kind := self.spin
    let i' := i + 1
    if let some start := memory[next]? then
      let loopLength := i' - start
      let target := (n - start) % loopLength + start
      if let some goal := memory.toList.find? (fun kv ↦ kv.snd == target) then
        goal.fst
      else
        dbg "Unreachable" next
    else
      loopTo' next n (memory.insert next i') i'
termination_by n - i

def loopTo (self : Rect Kind) (n : Nat) : Nat := loopTo' self n Std.HashMap.emptyWithCapacity 0 |>.evaluate

def solve (as : Array (Rect Kind)) : Nat := as.map (loopTo · 1000000000) |> sum

end Part2

public def solve := AocProblem.config 2023 14 parser.parse Part1.solve Part2.solve

end Y2023.Day14
