Data ← ⊜□≠@\n.&fras $"__data_2020_input-day08.txt" &var"AOC_REPO_DIR" ..Sep
Data ← ≡(⊂⊃(⊗∶{"acc" "jmp" "nop"}⊡0)(parse⊔⊡1))≡(⊜□≠@\s.⊔)Data
0 0 ∶≡(0;).Data # pc register instructions counts
Execute ← |3.3 ⊃((+1∶+⊙∶|+|+1;)⊃(⊃(⊡0)(⊡1)⊡⊙⋅∘)(⊙∘)) (⋅⋅∘)
&p $"Part1: _" ⊙;⊙;⋅∘⍢(|4.4 ⊃Execute(|4 ⍜⊡+ ∘⊙⊙1 ⊙⋅⋅∘))(=0⊡∶⊙⋅⋅∘)
