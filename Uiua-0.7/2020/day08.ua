Data ← ⊜□≠@\n.&fras $"__data_2020_input-day08.txt" &var"AOC_REPO_DIR" ..Sep
Data ← ≡(⊂⊃(⊗∶{"acc" "jmp" "nop"}⊡0)(parse⊔⊡1))≡(⊜□≠@\s.⊔)Data
Execute ← |3.3 ⊃((+1∶+⊙∶|+|+1;)⊃(⊃(⊡0)(⊡1)⊡⊙⋅∘)(⊙∘)) (⋅⋅∘)
Run ← ⍢(|4.4 ⊃Execute(|4 ⍜⊡+ ∘⊙⊙1 ⊙⋅⋅∘))(=0⊡⊙⋅⋅∘) 0 0 ∶≡(0;). # pc register instructions counts
&p $"Part1: _" ⊙;⊙;⋅∘Run Data
Completed ← ⧻ Data
RunToFinish ← ⊂⊙⊙(;;)⍢(|4.4 ⊃Execute(|4 ⍜⊡+ ∘⊙⊙1 ⊙⋅⋅∘))(|4 ↧↧⊃⊃(=0⬚1⊡⊙⋅⋅∘)(≥0)(<Completed)) 0 0 ∶≡(0;).
&p $"Part2: _" ⊡1⊢▽≡(=Completed⊡0).≡RunToFinish≐(⍜⊡-⊂∶0⊙⊙3)▽≐(≠0⊡0⊏) ,∶⇡⧻..Data
