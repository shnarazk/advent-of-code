import «AoC»
import Aesop

def main (args : List String) : IO Unit := do
  let day := (args.getD 0 "6").toNat!
  let extra := args.get? 1
  let result ← match day with
    | 1 => Aesop.time' $ day01 extra
    | 2 => Aesop.time' $ day02 extra
    | 3 => Aesop.time' $ day03 extra
    | 4 => Aesop.time' $ day04 extra
    | 5 => Aesop.time' $ day05 extra
    | 6 => Aesop.time' $ day06 extra
    | _ => Aesop.time' (return ())
  IO.println s!" => {result.printAsMillis}"
