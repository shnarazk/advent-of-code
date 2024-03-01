import «AoC»
import Aesop

def main : IO Unit := do
  let result ← Aesop.time' day02
  IO.println s!" => {result.printAsMillis}"
