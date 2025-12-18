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

/-- end of line -/
def eol : Parser Unit := pchar '\n' *> return ()

/-- repeat `p` separated by `s` -/
def sepBy1 (p : Parser α) (s : Parser β) : Parser (Array α) := do
  manyCore (attempt (s *> p)) #[←p]

/-- repeat `p` ended by `e` -/
def endBy (p : Parser α) (e : Parser β) : Parser (Array α) := do
  manyCore (attempt p) #[←p] <* e

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

-- #eval Parsec.run number "21, 8,"

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

-- #eval Parser.run number_signed "-21, 8,"

/-- single digit number -/
def single_digit := (·.toNat - '0'.toNat) <$> digit
-- #eval Parser.run single_digit "456"

namespace test

/-- alphabets followed by ':' -/
def label := many1Chars asciiLetter <* pchar ':'

-- #eval Parsec.run label "Game: 0, "

/-- sequence of "label: number" separated by "," -/
def fields := sepBy1 (separator₀ ' ' *> label *> separator ' ' *> number) (pchar ',')

-- #eval Parsec.run fields "a: 0, bb: 8"

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
