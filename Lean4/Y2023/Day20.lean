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

abbrev Circuit := HashMap Label (Mdl × Array Label)
 
def Circuit.new (rules : Array Rule) : Circuit :=
  rules.foldl
    (fun c r => 
       r.dests.foldl
         (fun c destLabel => 
           if let some target := c.get? destLabel then
             c.insert destLabel (r.module.link target.fst, target.snd)
           else
             c
          )
         c
    )
    (rules.foldl (fun c r => c.insert r.module.label (r.module, r.dests)) HashMap.empty)

instance : ToString Circuit where toString self := self.toList.toString

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

def solve (a : Array Rule) : Nat :=
  let c := Circuit.new a
  dbg s!"{c}" 0

end Part1

namespace Part2

def solve (_ : Array Rule) : Nat := 0

end Part2

def solve := AocProblem.config 2023 20
  ((dbg "parsed as ") ∘ parser.parse)
  Part1.solve
  Part2.solve

end Y2023.Day20
