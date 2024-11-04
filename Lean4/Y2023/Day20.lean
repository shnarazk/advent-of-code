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

instance : Hashable Mdl where
  hash
  | Mdl.Broadcaster => 0
  | Mdl.FlipFlop l b => hash (l, b)
  | Mdl.Conjunction l s => hash (l, s.toList)

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

def Circuit.toHashable (self : Circuit) (l : List Bool) : List Mdl × List Bool :=
  (self.circuit.toList.mergeSort (fun a b ↦ a.fst < b.fst) |>.map (·.snd.fst), l)

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

/-
Caveat: `partial` is not a silver-bullet.
We need to rewrite to use a decreasing counter explicitly.
-/
private partial def run_pulse' (circuit : Circuit) (queue : Queue) (dest_port : Label) (outputs : List Bool) (limit : Nat) : Circuit × List Bool :=
  match limit with
  | 0 => (circuit, outputs)
  | n + 1 =>
    if let some (pulse, q') := queue.dequeue? then
     let c' := if pulse.value then
          { circuit with pulse_h := circuit.pulse_h + 1 }
        else
          { circuit with pulse_l := circuit.pulse_l + 1 }
      if pulse.dest = dest_port then
        run_pulse' c' q' dest_port (outputs ++ [pulse.value]) (n + 1)
      else
        let (c'', q'') := c'.propagate q' pulse
        run_pulse' c'' q'' dest_port outputs n
    else
      (circuit, outputs)

def Circuit.run_pulse (circuit : Circuit) (dest_port : Label) (limit : Nat := 1000) : Circuit × List Bool :=
  run_pulse' circuit (Queue.empty.enqueue default) dest_port [] limit

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

partial def runUpto (circuit : Circuit) : Nat → Circuit
  | 0 => circuit
  | n + 1 => circuit.run_pulse "output" |> (runUpto ·.fst n)

def solve (a : Array Rule) : Nat :=
  runUpto (Circuit.new a) 1000 |> (fun c ↦ c.pulse_l * c.pulse_h)

end Part1

namespace Part2

partial def subcircuit' (circuit : Circuit) (visited : HashMap Label Node) :
    List Label → HashMap Label Node
  | [] => visited
  | root :: to_visit =>
    let senders : List Label := circuit.circuit.toList.filter
        (fun (_, node) ↦ node.snd.contains root)
      |>.map (·.fst)
    subcircuit'
      circuit
      (if let some r := circuit.get root then visited.insert root r else visited)
      (senders.foldl
        (fun l lbl ↦ if visited.contains lbl || l.contains lbl then l else lbl :: l)
        to_visit)

/-
Return a subcircuit consisted of all modules to compute root's value.
-/
def subcircuit (circuit : Circuit) (root : Label) : Circuit :=
  Circuit.mk (subcircuit' circuit HashMap.empty [root]) 0 0

abbrev CircuitState := List Mdl × List Bool

def LOOP_LIMIT := 8000

partial def findLoop' (dest : Label) (circuit : Circuit) (history : HashMap CircuitState Nat) (n : Nat) : Nat × Nat :=
  if LOOP_LIMIT < n then
    dbg s!"findLoop' dest:{dest}, n:{n} h:{history.size}" (0, 0)
  else
    let next : (Circuit × List Bool) := circuit.run_pulse dest
    let h : CircuitState := next.fst.toHashable next.snd
    -- if next.snd.getLast? == some true then
    if next.snd.contains true then
      if let some nstage := history.get? h then
        (nstage, n % (n - nstage))
      else
        findLoop' dest next.fst (history.insert h n) (n + 1)
    else
      findLoop' dest next.fst (history.insert h n) (n + 1)

/--
return loop_length × intro_length
-/
def findLoop (circuit : Circuit) (port : Label): Nat × Nat :=
  findLoop' port circuit HashMap.empty 1

/-
`rx` is the output of module `dh` and `dh` is a Conjunction module with four inputs.
So we need the cycle lengths of each input module states.
By using Chinese remain theorem, we can get the answer.
It is implemented as `Nat.chineseRemainder'` in Mathlib.Data.Nat.ModEq.
- {m n a b : ℕ} (h : a ≡ b [MOD n.gcd m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] }
-/
-- #eval Nat.chineseRemainder (by rfl : (21 : Nat).Coprime 19) 4 5
def crt (m n a b : Nat) : Nat :=
  if h : m.Coprime n then
    let c := Nat.chineseRemainder h a b
    if c == (0 : Nat) then m.lcm n else c
  else dbg s!"crt {m} {n} {a} {b} =>" $ m + a
-- #eval crt 21 17 4 5
-- #eval (277 - 4) / 21
-- #eval 21 * 13 + 4
-- #eval 17 * 16 + 5
-- #eval 13 * 16
-- #eval 277 % (13 * 16)
-- example : (crt 21 17 4 5) = 277 := by sorry
-- #eval crt 10002 10001 0 0
-- #eval (10002 : Nat).lcm 10001

def solve (a : Array Rule) : Nat :=
  let c := Circuit.new a
  if let some (lname, _) := c.circuit.toList.find? (fun (_, n) ↦ n.snd.contains "rx") then
    let targets := c.circuit.toList.filter (fun (_, n) ↦ n.snd.contains lname) |>.map (·.fst)
    let subcircuits : List (Label × Circuit) := targets.map (fun l ↦ (l, subcircuit c l))
    let lengths : List (Nat × Nat) := subcircuits.map (fun (_, c) ↦ findLoop c lname)
    lengths.tail.foldl (fun (m, a) (n, b) ↦
          if m.Coprime n then
            let tmp := crt m n a b
            let m' := (tmp - a) / m
            let n' := (tmp - b) / n
            (m' * n', tmp % (m' * n'))
          else
            (m, a))
        (lengths[0]!)
      |> (fun (a, b) ↦ a + b)
  else
    0
-- #eval (19 : Nat).Coprime 5
-- #eval (100030002 : Nat).Coprime 10012
-- #eval [2, 5, 8].tail

end Part2

def solve := AocProblem.config 2023 20 parser.parse Part1.solve Part2.solve

end Y2023.Day20
