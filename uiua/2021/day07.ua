Data ← ⊏⍏.⊜parse≠@,.⊔⊢⊜□≠@\n.&fras $"__data_2021_input-day07.txt" &var"AOC_REPO_DIR" ..Sep
Min ← /↧Data
Max ← /↥Data
Weight ← /+⌵-∶Data
WeightAcum ← /+≡(/+⇡+1)⌵-∶Data
&p$"Part1: _"⊡⊢⍏.≡Weight+Min ⇡-Min Max
&p$"Part2: _"⊡⊢⍏.≡WeightAcum+Min ⇡-Min Max
