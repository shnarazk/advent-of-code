import Batteries
import Std.Internal.Parsec

namespace AoCParser
open Lean
open Std.Internal
open Std.Internal.Parsec
open Std.Internal.Parsec.String

/--
end of line
--/
def eol : Parser Unit := pchar '\n' *> return ()

def sepBy1 (p : Parser α) (s : Parser β) : Parser (Array α) := do
  manyCore (attempt (s *> p)) #[←p]

def endBy (p : Parser α) (e : Parser β) : Parser (Array α) := do
  manyCore (attempt p) #[←p] <* e

/--
a sequence of space or TAB
--/
def whitespaces : Parser Unit := many1 (pchar ' ' <|> pchar '\t') *> return ()

/--
an optional sequence of space or TAB
--/
def whitespaces? : Parser Unit := many (pchar ' ' <|> pchar '\t') *> return ()

/--
[A-Za-z]+
--/
def alphabets := many1Chars asciiLetter

def separator (ch : Char)  : Parser Unit := many1 (pchar ch) *> return ()

def separator₀ (ch : Char)  : Parser Unit := optional (many (pchar ch)) *> return ()

/--
a `Nat`
--/
def number := do
  let s ← many1 digit
  return (Array.foldl (fun n (c : Char) => n * 10 + c.toNat - '0'.toNat) (0 : Nat) s)

-- #eval Parsec.run number "21, 8,"

/--
a signed number
--/
def number_p := do
  let s ← many1 digit
  return Int.ofNat (Array.foldl (fun n (c : Char) => n * 10 + c.toNat - '0'.toNat) (0 : Nat) s)

def number_m := do
  let n ← pchar '-' *> number_p
  return -n

def number_signed := number_m <|> number_p

-- #eval Parser.run number_signed "-21, 8,"

namespace test

def label := many1Chars asciiLetter <* pchar ':'

-- #eval Parsec.run label "Game: 0, "

def fields := sepBy1 (separator₀ ' ' *> label *> separator ' ' *> number) (pchar ',')

-- #eval Parsec.run fields "a: 0, bb: 8"

def parse := pstring "Game:" *> manyChars (pchar ' ') *> digit

-- #eval Lean.Parsec.run parse "Game: 0, "

def parsed (_source : String) : Nat := 0

end test

def parse (parser : Parser α) (source : String) : Option α :=
  match Parser.run parser source with
  | Except.ok r    => some r
  | Except.error _ => none

end AoCParser
