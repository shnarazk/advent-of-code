import Lean.Data.Parsec

namespace AoCParser
open Lean Parsec

/--
end of line
--/
def eol : Parsec Unit := pchar '\n' *> return ()

def sepBy1 (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  manyCore (attempt (s *> p)) #[←p]

/--
a sequence of space or TAB
--/
def whitespaces : Parsec Unit := many1 (pchar ' ' <|> pchar '\t') *> return ()

/--
an optional sequence of space or TAB
--/
def whitespaces? : Parsec Unit := many (pchar ' ' <|> pchar '\t') *> return ()

/--
[A-Za-z]+
--/
def alphabets := many1Chars asciiLetter

def separator (ch : Char)  : Parsec Unit := many1 (pchar ch) *> return ()

def separator₀ (ch : Char)  : Parsec Unit := optional (many (pchar ch)) *> return ()

/--
a `Nat`
--/
def number := do
  let s ← many1 digit
  return (Array.foldl (fun n (c : Char) => n * 10 + c.toNat - '0'.toNat) (0 : Nat) s)

#eval Parsec.run number "21, 8,"

namespace test

def label := many1Chars asciiLetter <* pchar ':'

#eval Parsec.run label "Game: 0, "

def fields := sepBy1 (separator₀ ' ' *> label *> separator ' ' *> number) (pchar ',')

#eval Parsec.run fields "a: 0, bb: 8"

def parse := pstring "Game:" *> manyChars (pchar ' ') *> digit

#eval Lean.Parsec.run parse "Game: 0, "

def parsed (_source : String) : Nat := 0

end test

def parse (parser : Parsec a) (source : String) : Option a :=
  match Parsec.run parser source with
  | Except.ok r    => some r
  | Except.error _ => none

end AoCParser
