import «AoC»
import Aesop

def main (args : List String) : IO Unit := do
  IO.println s!"{args}"
  -- let result ← Aesop.time' day01
  -- let result ← Aesop.time' day02
  -- let result ← Aesop.time' day03
  let result ← Aesop.time' day04
  -- let result ← Aesop.time' day05
  IO.println s!" => {result.printAsMillis}"
