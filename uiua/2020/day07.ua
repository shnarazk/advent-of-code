Data ← ⊜□≠@\n.&fras $"__data_2020_input-day07.txt" &var"AOC_REPO_DIR" ..Sep
Data ← ≡(□⊂"1 "▽¬⍥(↥⊃∘(↻¯1))7⌕"contain ".▽¬↻¯7⌕"contains".▽¬↻¯3⌕"bags".▽¬∊∶",.".⊔)Data
Data ← ≡(□≡(⊂⊃((parse⊔⊡0|0;)≍{"no" "other"}.)(□⊐/⊂↘1)⊜□≠@\s.⊔)⊜□¬⍥(↥⊃∘(↻¯1))2⌕"bag".⊔)Data
Data ← ≡(□▽≡(≠0⊔⊡0⊔).⊔)Data
Names ← ⊏⍏.⊝⊐≡(⊡1)/(⊐⊂∩⊔)Data
ShinyGold ← ⊗□"shinygold"Names
Data ← ≡(□≡(⊂⊃(⊔⊡0)(⊗∶Names ⊡1))⊔)⊔ Data

Contains ← /↥≐(=⊡1)↘1
---
⍤ "contains"Contains [1_10 1_200 2_400] 200
⍤ "contains"¬ Contains [1_10 1_200 2_400] 10
---

Upstream ← ([];|[⊡1⊡0])(∘|0;)≍[¯∞ ¯∞]./↥≐(=⊡1)↘1,∶⊔
---
⍤ "upstream"≍[10] Upstream [1_10 1_200 2_400] 200
⍤ "upstream"≍[] Upstream [1_10 1_200 2_400] 10
---

Parents ← ⊐/⊂≐(□Upstream)Data

&p $"Part1: _" -1⧻⊙;⍢(|2.2 ⊏⍏.⊝⊐⊂,⊔⊃(⊐/⊂∵(□Parents))(⟜∘))(|2 ¬≍)[ShinyGold][]
Fetch ← (↘1⊔⊏∶Data⊢⊚=∶≡(⊡1⊡0⊔)⊔Data)
&p $"Part2: _" -1;⍢(?(;;)(⊂∺×⊂∶1∶)=0⧻.Fetch⊃(⊙⊙∘)(+⋅⊙⋅∘)⊃(⊃(⊡1)(⊡0)⊢)(↘1))(>0⧻) [[1 ShinyGold]] 0
