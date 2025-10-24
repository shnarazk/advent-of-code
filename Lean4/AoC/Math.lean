partial
def gcd (x y : Int) : Int := if y = 0 then x else gcd y (x % y)

-- #eval gcd 10 5

partial
def lcm (x y : Int) : Int := (x * y) % gcd x y

partial
def solve (i a m : Int) : Int :=
 if (i * a) % m = 1 then i else solve (i + 1) a m

/--
Chinese Remainder Theorem
```
crt ⟨5, 4⟩ ⟨2, 0⟩ |>.snd = 14
```
-/
partial
def chinese_remainder_theorem (aq_ar bq_br : Int × Int) : Int × Int :=
  let (aq, ar) := aq_ar
  let (bq, br) := bq_br
  if ar = 0 ∧ br = 0 then ⟨lcm aq bq, 0⟩
  else
    let n := solve 0 aq bq
    let nar := (n * ar) % bq
    let nbr := (n * br) % bq
    let m := if nar < nbr then nbr - nar else bq + nbr - nar
    ⟨aq * bq, aq * m + ar⟩

-- #eval chinese_remainder_theorem ⟨5, 4⟩ ⟨2, 0⟩ |>.snd
-- #eval chinese_remainder_theorem ⟨21, 4⟩ ⟨17, 5⟩ |>.snd
