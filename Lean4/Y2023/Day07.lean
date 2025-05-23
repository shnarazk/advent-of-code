import «AoC».Basic
import «AoC».Parser

namespace Y2023.Day07

structure Hand where
  hand ::
  cards : Array Char
  bid   : Nat
deriving BEq, Inhabited, Repr

namespace parser

open Lean AoCParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String

def card := digit <|> pchar 'A' <|> pchar 'K' <|> pchar 'Q' <|> pchar 'J' <|> pchar 'T'
def cards := many1 card <* whitespaces
def line : Parser Hand := (return Hand.hand) <*> cards <*> number
def parse := AoCParser.parse $ sepBy1 line eol

end parser

def solve1_line (_line : String) : Nat := 0

def uniqueChars (cs : Array Char) : List Char :=
  Array.foldl (fun l e => if l.contains e then l else e :: l) [] cs

def occurences (cs : Array Char) : Array Nat :=
  uniqueChars cs
    |>.map (fun c => (cs.filter (· == c)).size)
    |>.toArray
    |>.qsortOrd
    |>.reverse

-- #eval occurences #['A', '3', '9', 'A', 'A']

/--
larger is higher
-/
def order₁ : Char -> Nat
  | 'A' => 14
  | 'K' => 13
  | 'Q' => 12
  | 'J' => 11
  | 'T' => 10
  | '9' => 9
  | '8' => 8
  | '7' => 7
  | '6' => 6
  | '5' => 5
  | '4' => 4
  | '3' => 3
  | '2' => 2
  | _ => 0

-- #eval order₁ 'A'

def orderOf (order : Char -> Nat) (h : Hand) : Array Nat := Array.map order h.cards

def evaluation (h : Hand) : (Nat × List Nat) × Nat :=
  let ord := orderOf order₁ h |> Array.toList
  match occurences h.cards with
  | #[5]          => ((7, ord), h.bid) -- Five of a kind
  | #[4, 1]       => ((6, ord), h.bid) -- Four of a kind
  | #[3, 2]       => ((5, ord), h.bid) -- Full house
  | #[3, 1, 1]    => ((4, ord), h.bid) -- Three of a kind
  | #[2, 2, 1]    => ((3, ord), h.bid) -- Two pair
  | #[2, 1, 1, 1] => ((2, ord), h.bid) -- One pair
  | _             => ((1, ord), h.bid) -- High card

-- #eval evaluation <| Hand.hand #['A', '3', '9', 'A', 'A'] 33

def compareList (a b : List Nat) : Ordering :=
  match a, b with
  | [], []             => .eq
  | [], _              => .lt
  | _, []              => .lt
  | a₀ :: a', b₀ :: b' =>
    if a₀ == b₀
    then compareList a' b'
    else compare a₀ b₀

-- #eval compareList [2, 4] [2, 4] == Ordering.eq
-- #eval compareList [2, 3, 1] [2, 1] == Ordering.gt

def solve1 (d : Array Hand) : Nat :=
  let o := Array.qsort (d.map evaluation) (fun a b =>
    match compare a.fst.fst b.fst.fst, compareList a.fst.snd b.fst.snd with
    | Ordering.eq, ord => ord == Ordering.lt
    | ord, _ => ord == Ordering.lt)
  o.foldl (fun acc r => (acc.fst + acc.snd * r.snd, acc.snd + 1)) (0, 1)
    |>.fst

def order₂ : Char -> Nat
  | 'A' => 14
  | 'K' => 13
  | 'Q' => 12
  | 'J' => 1
  | 'T' => 10
  | '9' => 9
  | '8' => 8
  | '7' => 7
  | '6' => 6
  | '5' => 5
  | '4' => 4
  | '3' => 3
  | '2' => 2
  | _ => 0

def evaluation₂ (h : Hand) : (Nat × List Nat) × Nat :=
  let ord := orderOf order₂ h |> Array.toList
  let num_J := Array.filter (. == 'J') h.cards |> Array.size
  let cardsJ := Array.filter (· != 'J') h.cards
  let occurs := occurences cardsJ
  -- Lean-4.15 requires the following check!!!
  if occurs.size == 0
    then ((7, ord), h.bid)
  else
    let oc := if num_J == 5 then #[5] else Array.modify occurs 0 (. + num_J)
    match oc with
    | #[5]          => ((7, ord), h.bid) -- Five of a kind
    | #[4, 1]       => ((6, ord), h.bid) -- Four of a kind
    | #[3, 2]       => ((5, ord), h.bid) -- Full house
    | #[3, 1, 1]    => ((4, ord), h.bid) -- Three of a kind
    | #[2, 2, 1]    => ((3, ord), h.bid) -- Two pair
    | #[2, 1, 1, 1] => ((2, ord), h.bid) -- One pair
    | _             => ((1, ord), h.bid) -- High card

-- #eval evaluation₂ <| Hand.hand #['A', '3', '9', 'J', 'A'] 33

def solve2 (d : Array Hand) : Nat :=
  let o := Array.qsort (d.map evaluation₂) (fun a b =>
    match compare a.fst.fst b.fst.fst, compareList a.fst.snd b.fst.snd with
    | Ordering.eq, ord => ord == Ordering.lt
    | ord        , _   => ord == Ordering.lt)
  let winnings := Array.foldl (fun acc r => (acc.fst + acc.snd * r.snd, acc.snd + 1)) (0, 1) o
  winnings.fst

def solve := AocProblem.config 2023 7 parser.parse solve1 solve2

end Y2023.Day07
