import Mathlib.Data.Nat.ModEq
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

abbrev Node := Mdl × Array Label

structure Circuit where
  circuit : HashMap Label Node
  pulse_l : Nat
  pulse_h : Nat

def Circuit.get (self : Circuit) (lebel : Label) : Option Node := self.circuit.get? lebel

def Circuit.insert (self : Circuit) (label : Label) (node : Node) :=
  { self with circuit := self.circuit.insert label node }

def Circuit.new (rules : Array Rule) : Circuit :=
  rules.foldl
    (fun c r ↦
      r.dests.foldl
        (fun c dest ↦
          if let some (Mdl.Conjunction l s, d') := c.get dest then
            c.insert dest (Mdl.Conjunction l (s.insert r.module.label false), d')
          else
            c
        )
        c)
    (rules.foldl
      (fun c r => c.insert r.module.label (r.module, r.dests))
      (Circuit.mk HashMap.empty 0 0))

abbrev Queue := Std.Queue Pulse

def Circuit.propagate (self : Circuit) (queue : Queue) (pulse : Pulse): Circuit × Queue :=
  if let some (m, dests) := self.get pulse.dest then
    let (m', output) := m.pulse (pulse.source, pulse.value)
    (
      self.insert m.label (m', dests),
      if let some (label, value) := output then
        dests.foldl (fun q dest ↦ q.enqueue (Pulse.mk label dest value)) queue
      else
        queue)
  else
    (self, queue)

instance : ToString Circuit where toString self := s!"{self.pulse_l}:{self.pulse_h}\n{self.circuit.toList.toString}"

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

partial def subcircuit' (circuit : Circuit) (visited : HashMap Label Node) :
    List Label → HashMap Label Node
  | [] => visited
  | root :: to_visit =>
    let senders : List (Label × Node) := circuit.circuit.toList.filter
        (fun (_, node) ↦ node.snd.contains root)
    subcircuit'
      circuit
      (if let some r := circuit.get root then visited.insert root r else visited)
      (senders.foldl
        (fun l ln ↦ if visited.contains ln.fst || l.contains ln.fst then l else ln.fst :: l) to_visit)

/-
Return a subcircuit consisted of all modules to compute root's value.
-/
def subcircuit (circuit : Circuit) (root : Label) : Circuit :=
  Circuit.mk (subcircuit' circuit HashMap.empty [root]) 0 0

/-
`rx` is the output of module `dh` and `dh` is a Conjunction module with four inputs.
So we need the cycle lengths of each input module states.
By using Chinese remain theorem, we can get the answer.
It is implemented as `Nat.chineseRemainder'` in Mathlib.Data.Nat.ModEq.
- {m n a b : ℕ} (h : a ≡ b [MOD n.gcd m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] }
-/
-- #eval Nat.chineseRemainder (by rfl : (21 : Nat).Coprime 19) 4 5
def crt (m n a b : Nat) : Nat := if h : m.Coprime n then Nat.chineseRemainder h a b else 0
-- #eval crt 21 17 4 5
-- example : (crt 21 17 4 5) = 277 := by sorry

def solve (a : Array Rule) : Nat :=
  let c := Circuit.new a
  if let some (lname, _) := c.circuit.toList.find? (fun (_, n) ↦ n.snd.contains "rx") then
    let targets := c.circuit.toList.filter (fun (_, n) ↦ n.snd.contains lname)
    let subcircuits : List Circuit := (dbg "4" targets).map (subcircuit c ·.fst)
    dbg s!"get rx: {subcircuits.map (·.circuit.size)}" 0
  else
    0

end Part2

def solve := AocProblem.config 2023 20 parser.parse Part1.solve Part2.solve

end Y2023.Day20
