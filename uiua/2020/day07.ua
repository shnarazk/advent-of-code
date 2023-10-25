Data ← ⊜□≠@\n.&fras $"__data_2020_input-day07.txt" &var"AOC_REPO_DIR" ..Sep
Data ← ≡(□⊂"1 "▽¬⍥(↥⊃'⊂∶⊂0)7⌕"contain ".▽¬⊂⬚0↙7[]⌕"contains".▽¬⊂⬚0↙3[]⌕"bags".▽¬∊∶",.".⊔)Data
Data ← ≡(□≡(⊂⊃((parse⊡0|0;)≍{"no" "other"}.)(□⊐/⊂↘1)⊜□≠@\s.⊔)⊜□¬⍥(↥⊃'⊂∶⊂0)2⌕"bag".⊔)Data
Data ← ⊐≡(□▽≡(≠0⊡0).)Data
Names ← ⊏⍏.⊝≡(⊡1)/(⊂∩⊔)Data
ShinyGold ← ⊗□"shinygold"Names
# &p $"Names\n_" Names
Data ← ≡(□≡(⊂⊃(⊔⊡0)(⊗ ∶Names ⊡1))⊔)⊔ Data

Contains ← /↥≐(=⊡1)↘1
---
⍤ "contains"Contains [1_10 1_200 2_400] 200
⍤ "contains"¬ Contains [1_10 1_200 2_400] 10
---

Upstream ← ([];|[⊡1⊡0])(∘|0;)≍[¯∞ ¯∞]./↥≐(=⊡1)↘1,∶⊔
---
⍤ "upstream"≍ [10] Upstream [1_10 1_200 2_400] 200
⍤ "upstream"≍[] Upstream [1_10 1_200 2_400] 10
---

Parents ← ⊐/⊂ ≐'□Upstream Data
&p $"Part1: _" -1⧻⍥(⎋≍,∶⊏⍏.⊝⊐⊂,⊔⊐/⊂∵'□Parents.)∞[ShinyGold]
