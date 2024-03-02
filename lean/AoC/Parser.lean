import Lean.Data.Parsec

open Lean Parsec

def eol : Parsec Unit := pchar '\n' *> return ()

def manySep (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  manyCore (attempt (s *> p)) #[←p]

def separator (ch : Char)  : Parsec Unit := many1 (pchar ch) *> return ()

def separator₀ (ch : Char)  : Parsec Unit := optional (many (pchar ch)) *> return ()

def number := do
  let s ← many1 digit
  return (Array.foldl (fun n (c : Char) => n * 10 + c.toNat - '0'.toNat) (0 : Nat) s)

#eval Parsec.run number "21, 8,"

namespace test

def label := many1Chars asciiLetter <* pchar ':'

#eval Parsec.run label "Game: 0, "

def fields := manySep (separator₀ ' ' *> label *> separator ' ' *> number) (pchar ',')

#eval Parsec.run fields "a: 0, bb: 8"

def parse := pstring "Game:" *> manyChars (pchar ' ') *> digit

#eval Lean.Parsec.run parse "Game: 0, "

def parsed (_source : String) : Nat := 0

end test
