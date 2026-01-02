module

public import Batteries
public import Std.Internal.Parsec

@[expose] public section

namespace AoCParser
open Lean
open Std.Internal
open Std.Internal.Parsec
open Std.Internal.Parsec.String

variable {α β γ : Type}

instance {ε : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq a b := match a, b with
  | .error x, .error y => x == y
  | .ok x, .ok y => x == y
  | _ , _ => false

/-- end of line -/
def eol : Parser Unit := pchar '\n' *> return ()

/-- repeat `p` separated by `s` -/
def separated (p : Parser α) (s : Parser β) : Parser (Array α) := do
  manyCore (attempt (s *> p)) #[←p]

/-- repeat `p`. This is `repeat` in Winnow. But it's reserved keyword in Lean4. -/
def repeated (p : Parser α) : Parser (Array α ) := do manyCore (attempt p) #[←p]

/-- repeat `p` ended by `e`. Return both. -/
def repeatTill (p : Parser α) (e : Parser β) : Parser (Array α × β) := do
  (fun a b ↦ (a, b)) <$> manyCore (attempt p) #[←p] <*> e

/-- a sequence of space or TAB -/
def whitespaces : Parser Unit := many1 (pchar ' ' <|> pchar '▸') *> return ()

/-- an optional sequence of space or TAB -/
def whitespaces? : Parser Unit := many (pchar ' ' <|> pchar '▸') *> return ()

/-- [A-Za-z]+ -/
def alphabets := many1Chars asciiLetter

/-- repeat `ch` and discard the result -/
def separator (ch : Char) : Parser Unit := many1 (pchar ch) *> return ()

/-- repeat `ch` zero or more times and discard the result -/
def separator₀ (ch : Char) : Parser Unit := optional (many (pchar ch)) *> return ()

/-- a `Nat` -/
def number : Parser Nat := do
  let s ← many1 digit
  return (Array.foldl (fun n (c : Char) => n * 10 + c.toNat - '0'.toNat) (0 : Nat) s)

#guard Parser.run number "21, 8," == Except.ok 21

/-- a signed number -/
def number_p : Parser Int := do
  let s ← many1 digit
  return Int.ofNat (Array.foldl (fun n (c : Char) => n * 10 + c.toNat - '0'.toNat) (0 : Nat) s)

/-- a nugative integer -/
def number_m : Parser Int := do
  let n ← pchar '-' *> number_p
  return -n

/-- a negative or non-negative integer -/
def number_signed : Parser Int := number_m <|> number_p

#guard (Parser.run number_signed "-21, 8,") == Except.ok (-21)

/-- single digit number -/
def single_digit := (·.toNat - '0'.toNat) <$> digit

#guard Parser.run single_digit "456" == Except.ok 4

namespace test

/-- alphabets followed by ':' -/
def label := many1Chars asciiLetter <* pchar ':'

#guard Parser.run label "Game: 0, " == Except.ok "Game"

/-- sequence of "label: number" separated by "," -/
def fields := separated (separator₀ ' ' *> label *> separator ' ' *> number) (pchar ',')

#guard Parser.run fields "a: 0, bb: 8" == Except.ok #[0, 8]

-- def parse := pstring "Game:" *> manyChars (pchar ' ') *> digit
-- #eval Lean.Parsec.run parse "Game: 0, "
-- def parsed (_source : String) : Nat := 0

end test

/-- Run `parser` on `source` and return the result as `Option` -/
def parse (parser : Parser α) (source : String) : Option α :=
  match Parser.run parser source with
  | Except.ok r    => some r
  | Except.error _ => none

end AoCParser
