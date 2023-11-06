Data ← ⊜□≠@\n.&fras $"__data_2020_input-day08-test.txt" &var"AOC_REPO_DIR" ..Sep
Data ← ≡(⊂⊃(⊗∶{"acc" "jmp" "nop"}⊡0)(parse⊔⊡1))≡(⊜□≠@\s.⊔)Data
Execute ← |3.3 ⊃((+1∶+⊙∶|+|+1;)⊃(⊃(⊡0)(⊡1)⊡⊙⋅∘)(⊙∘)) (⋅⋅∘)
Run ← ⍢(|4.4 ⊃Execute(|4 ⍜⊡+ ∘⊙⊙1 ⊙⋅⋅∘))(=0⊡∶⊙⋅⋅∘dump∘) 0 0 ∶≡(0;). # pc register instructions counts
&p $"Part1: _" ⊙;⊙;⋅∘Run Data
Completed ← ⧻ Data
# RunToFinish ← ⍢(|4.4 dump∘⊃Execute(|4 ⍜⊡+ ∘⊙⊙1 ⊙⋅⋅∘))(|4 ↧↧⊃⊃(=0⊡∶⊙⋅⋅∘)(≥0)(<Completed)dump∘)dump∘ 0 0 ∶≡(0;). # pc register instructions counts
# RunToFinish ← ⍢(|4.4 ⊃Execute(|4 ⍜⊡+ ∘⊙⊙1 ⊙⋅⋅∘))(↥⊃(=0⊡∶⊙⋅⋅∘)(|1 =Completed dump∘)) 0 0 ∶≡(0;). # pc register instructions counts
# &p ≡RunToFinish≐(⍜⊡-2∶)▽≐(≠1⊡0⊏) ,∶⇡⧻..Data
