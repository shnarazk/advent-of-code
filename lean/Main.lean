import «AoC»
import Aesop

def main : IO Unit := do
  let result ← Aesop.time' day01
  IO.println s!" => {result.printAsMillis}"
