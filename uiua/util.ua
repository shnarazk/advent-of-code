ParseInts ← (|1 □⊜parse∊∶"0123456789-".!)

# |(1+N). reverse top N items in stack
# ReverseStack 4 (⇌) 2_2 1_1 0_0_0 → 0_0_0 1_1 2_2 (⇌)
ReverseStack ← /!⍥'⊂→□-1→□

# Unacceptable function signature
# |(1+N). collect top N items into a list
# Merge 4 (⇌) 2_2 1_1 0_0_0 → [(⇌) 2_2 1_1 0_0_0]
# Merge ← ⍥'⊂→□-1→□
