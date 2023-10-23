ParseInts ← (|1 ⊜parse∊∶"0123456789-".)
---
⍤ "parse ints"≍ [1 30] ParseInts " 1 30 "
---

# # |(1+N). reverse top N items in stack
# ReverseStack ← /⇌⍥'⊂⊙□-1⊙□
# ---
# ⍤ "reversestackt" ≍[0_0_0 1_1 2_2] dump∘ ReverseStack 2 2_2 1_1 0_0_0
# ---

# Unacceptable function signature
# |(1+N). collect top N items into a list
# Merge 4 (⇌) 2_2 1_1 0_0_0 → [(⇌) 2_2 1_1 0_0_0]
# Merge ← ⍥'⊂→□-1→□

Ord ← ?⊙∘∶≥,,
---
⍤ "ord"≍0 ⊙;Ord 0 1
---

GCDrecur ← |2.2 ?⊙∘(|2.2 ⊃(◿)(∘)) =0.Ord

GCD ← |2 ;⍥(|2.2 ⎋=0.GCDrecur)∞
---
⍤ "gcd" ≍5 GCD 10 5
⍤ "gcd" ≍5 GCD 5 10
⍤ "gcd" ≍10 GCD 50 20
---
