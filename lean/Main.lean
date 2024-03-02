import «AoC»
import Aesop

def main (args : List String) : IO Unit := do
  let day := (args.getD 0 "6").toNat!
  let result ← match day with
    | 1 => Aesop.time' day01
    | 2 => Aesop.time' day02
    | 3 => Aesop.time' day03
    | 4 => Aesop.time' day04
    | 5 => Aesop.time' day05
    | 6 => Aesop.time' day06
    | _ => Aesop.time' (return ())
  IO.println s!" => {result.printAsMillis}"
