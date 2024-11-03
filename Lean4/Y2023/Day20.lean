import «AoC».Basic
import «AoC».Combinator
import «AoC».Parser

namespace Y2023.Day20

open Accumulation CiCL
open Std

abbrev HashMap := Std.HashMap
abbrev Label := String

structure Input where
deriving BEq, Repr
instance : ToString Input where toString _ := s!""

inductive Mdl where
  | Broadcaster
  | FlipFlop (label : Label) (state : Bool)
  | Conjunction (label : Label) (state : HashMap Label Bool)

instance : BEq Mdl where
  beq : Mdl → Mdl → Bool
  | .Broadcaster     , .Broadcaster      => true
  | .FlipFlop l₁ _   , .FlipFlop l₂ _    => l₁ == l₂
  | .Conjunction l₁ _, .Conjunction l₂ _ => l₁ == l₂
  | _                , _                 => false

instance : ToString Mdl where
  toString : Mdl → String
    | Mdl.Broadcaster     => "Broadcaster"
    | Mdl.FlipFlop l s    => s!"FF:{l}({s})"
    | Mdl.Conjunction l s => s!"Con:{l}({s.toList})"
-- #eval Mdl.FlipFlop "ab"
-- #eval Mdl.Conjunction "ab"

def Mdl.label : Mdl → Label
  | Mdl.Broadcaster    => "broadcaster"
  | Mdl.FlipFlop l _    => l
  | Mdl.Conjunction l _ => l

def Mdl.pulse : Mdl → (Label × Bool) → Mdl × Option (Label × Bool)
  | Mdl.Broadcaster,           _ => (Mdl.Broadcaster, some ("broadcaster", false))
  | Mdl.FlipFlop l b, (_, false) => (Mdl.FlipFlop l !b   , some (l, !b))
  | Mdl.FlipFlop l b,  (_, true) => (Mdl.FlipFlop l b    , none)
  | Mdl.Conjunction l s, (l', b) =>
     let s' := s.insert l' b      ; (Mdl.Conjunction l s', some (l, !s'.values.all I))
-- #eval (Mdl.FlipFlop "ff" false).pulse ("a", false)

def Mdl.link : Mdl → Mdl → Mdl
  | Mdl.Broadcaster     , Mdl.Conjunction l s => Mdl.Conjunction l (s.insert "" false)
  | Mdl.FlipFlop l' _   , Mdl.Conjunction l s => Mdl.Conjunction l (s.insert l' false)
  | Mdl.Conjunction l' _, Mdl.Conjunction l s => Mdl.Conjunction l (s.insert l' false)
  | _                   , d                   => d

structure Rule where
  module : Mdl
  dests  : Array String

instance : ToString Rule where
  toString r := s!"{r.module} -> {r.dests}"

structure Pulse where
  source : Label
  dest   : Label
  value  : Bool
deriving BEq

instance : Inhabited Pulse where
  default := Pulse.mk "button" "broadcaster" false

instance : ToString Pulse where
  toString p := s!"{p.source} -{if p.value then "high" else "low"}-> {p.dest}"

structure Circuit where
  circuit : HashMap Label (Mdl × Array Label)
  pulse_l : Nat
  pulse_h : Nat
  out_l : Nat
  out_h : Nat

def Circuit.new (rules : Array Rule) : Circuit :=
  rules.foldl
    (fun c r ↦
      r.dests.foldl
        (fun c dest ↦
          if let some (Mdl.Conjunction l s, d') := c.circuit.get? dest then
            { c with
              circuit := c.circuit.insert dest (Mdl.Conjunction l (s.insert r.module.label false), d') }
          else
            c
        )
        c
      )
    (rules.foldl
      (fun c r => { c with
          circuit := c.circuit.insert r.module.label (r.module, r.dests)})
      (Circuit.mk HashMap.empty 0 0 0 0))

abbrev Queue := Std.Queue Pulse

def Circuit.propagate (self : Circuit) (queue : Queue) (pulse : Pulse): Circuit × Queue :=
  if let some (m, dests) := self.circuit.get? pulse.dest then
    let (m', output) := m.pulse (pulse.source, pulse.value)
    (
      { self with circuit := self.circuit.insert m.label (m', dests) },
      if let some (label, value) := output then
        dests.foldl (fun q dest ↦ q.enqueue (Pulse.mk label dest value)) queue
      else
        queue)
  else
    (self, queue)

instance : ToString Circuit where toString self := s!"{self.out_l}:{self.out_h}\n{self.circuit.toList.toString}"

namespace parser

open AoCParser
open Std
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def pmodule := pbroadcaster <|> pflipflop <|> pconjunction
  where
    pbroadcaster := pstring "broadcaster"  *> return Mdl.Broadcaster
    pflipflop := do
      let l ← pchar '%' *> alphabets
      return Mdl.FlipFlop l false
    pconjunction := do
      let l ← pchar '&' *> alphabets
      return Mdl.Conjunction l HashMap.empty

-- #eval AoCParser.parse pmodule "broadcaster"
-- #eval AoCParser.parse pmodule "%a"
-- #eval AoCParser.parse pmodule "&inv"

def pdests := sepBy1 alphabets (pstring ", ")
-- #eval AoCParser.parse pdests  "a"
-- #eval AoCParser.parse .dests "a, b, c"

def pline := do
  let m ← pmodule <* whitespaces <* pstring "->" <* whitespaces
  let o ← pdests
  return Rule.mk m o
-- #check pline
-- #eval AoCParser.parse pline "%a -> inv, con"

def parse : String → Option (Array Rule) := AoCParser.parse parser
  where
    parser := sepBy1 pline eol
-- #eval parse "%a -> inv, con\n&inv -> b"

end parser

namespace Part1

partial def runUpto (circuit : Circuit) (queue : Queue) (n : Nat) : Circuit :=
  if let some (pulse, q') := queue.dequeue? then
    let c' := if pulse.value then
        { circuit with pulse_h := circuit.pulse_h + 1 }
      else
        { circuit with pulse_l := circuit.pulse_l + 1 }
    let next := c'.propagate q' pulse -- (dbg s!"{n}" pulse)
    runUpto next.fst next.snd n
  else match n with
    | 0 => circuit
    | n' + 1 => runUpto circuit (queue.enqueue (default : Pulse)) n'

def solve (a : Array Rule) : Nat :=
  runUpto (Circuit.new a) (Queue.empty.enqueue (default : Pulse)) (1000 - 1)
    |> (fun c ↦ c.pulse_l * c.pulse_h)

end Part1

namespace Part2

def solve (a : Array Rule) : Nat :=
  let c := dbg "circuit" $ Circuit.new a
  dbg s!"{c.pulse_h}" 0

end Part2

def solve := AocProblem.config 2023 20 parser.parse Part1.solve Part2.solve

end Y2023.Day20
