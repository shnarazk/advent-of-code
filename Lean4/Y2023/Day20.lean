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
  | Mdl.Broadcaster    => ""
  | Mdl.FlipFlop l _    => l
  | Mdl.Conjunction l _ => l

def Mdl.pulse : Mdl → (Label × Bool) → Mdl × Option (Label × Bool)
  | Mdl.Broadcaster,           _ => (Mdl.Broadcaster     , some ("", false))
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
  default := Pulse.mk "" "" false

structure Circuit where
  circuit : HashMap Label (Mdl × Array Label)
  out_l : Nat
  out_h : Nat

def Circuit.new (rules : Array Rule) : Circuit :=
  rules.foldl
    (fun c r =>
       r.dests.foldl
          (fun c destLabel =>
            if let some target := c.circuit.get? destLabel then
              { c with
                circuit := c.circuit.insert
                    destLabel
                    (r.module.link target.fst, target.snd)
              }
            else
              c
          )
         c
    )
    (rules.foldl
      (fun c r => { c with
          circuit := c.circuit.insert r.module.label (r.module, r.dests)})
      (Circuit.mk HashMap.empty 0 0))

abbrev Queue := Std.Queue Pulse

def Circuit.propagate (self : Circuit) (queue : Queue) (pulse : Pulse): Circuit × Queue :=
  if let some (m, dests) := self.circuit.get? pulse.dest then
    let (m', output) := m.pulse (pulse.source, pulse.value)
    (
      if dests.contains "output" then
        match output with
          | none => { self with circuit := self.circuit.insert m.label (m', dests) }
          | some (_, false) =>
            { self with
              circuit := self.circuit.insert m.label (m', dests)
              out_l := self.out_l + 1 }
          | some (_, true) =>
            { self with
              circuit := self.circuit.insert m.label (m', dests)
              out_h := self.out_h + 1 }
      else
        { self with circuit := self.circuit.insert m.label (m', dests) },
     if let some (label, value) := output then
        dests.foldl (fun q dest ↦
            if dest != "output" then q.enqueue (Pulse.mk label dest value) else q)
          queue
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

partial def runUpto (circuit : Circuit) (queue : Queue) : (n : Nat) → Circuit
  | 0 => circuit
  | n + 1 =>
    if let some (pulse, q') := queue.dequeue? then
      let next := circuit.propagate q' pulse
      runUpto next.fst next.snd (n + 1)
    else
      runUpto circuit (queue.enqueue (default : Pulse)) n

def solve (a : Array Rule) : Nat :=
  let c := Circuit.new a
  let q := Queue.empty.enqueue (default : Pulse)
  let c' := runUpto c q 4000
  dbg s!"{c}" $ c'.out_l * c'.out_h

end Part1

namespace Part2

def solve (_ : Array Rule) : Nat := 0

end Part2

def solve := AocProblem.config 2023 20
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day20
