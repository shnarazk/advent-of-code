Data ← ∵(⊜parse¬∊," ,->"⊔)⊜□≠@\n.&fras $"__data_2021_input-day05.txt" &var"AOC_REPO_DIR" ..Sep

↕ ← ×⊃(⇡+1⌵)±
---
⍤ "extended range" ≍ [0 1 2 3] ↕3
⍤ "extended range" ≍ [0 ¯1 ¯2 ¯3] ↕¯3
---

LineHV ← |1 (⊙;∘≡(⊂:)⊙(+⊙(↕-).):|≡⊂⊙(+⊙(↕-).)⊙⊙⋅∘)⊃⊃⊃⊃(/=⊏0_2)(⊡0)(⊡1)(⊡2)(⊡3)
# LineHV ← |1 (⊙;∘∺(⊂:)⊙(+⊙(↕-).):|∺⊂⊙(+⊙(↕-).)⊙⊙⋅∘)⊃⊃⊃⊃(/=⊏0_2)(⊡0)(⊡1)(⊡2)(⊡3)
---
⍤ "LineHV" ≍ [1_1 1_2 1_3] LineHV [1 1 1 3]
⍤ "LineHV" ≍ [260_1 260_2 260_3] LineHV [260 1 260 3]
⍤ "LineHV" ≍ ∩(⊏⍏.)[260_1 260_2 260_3 260_4] LineHV [260 4 260 1]
⍤ "LineHV" ≍ [1_0 2_0 3_0] LineHV [1 0 3 0]
⍤ "LineHV" ≍ [1_8 2_8 3_8] LineHV [1 8 3 8]
---

LineOr ← (|1 ⍉⊟⊃(+⊙(↕-).⊃(⊡0)(⊡2))(+⊙(↕-).⊃(⊡1)(⊡3)))
---
⍤ "LineOr" ≍ [1_1 2_2 3_3] LineOr [1 1 3 3]
⍤ "LineOr" ≍ [260_4 261_3 262_2 263_1] LineOr [260 4 263 1]
---

PartOne ← ∧(⊂⊙LineHV:): ↯0_2[] ▽≡(↥⊃(/=⊏0_2)(/=⊏1_3)).Data
&p$"Part1: _"/+>1⍘⊚⊗:⊝.PartOne
&p$"Part2: _"/+>1⍘⊚⊗:⊝.∧(⊂⊙LineOr:) :PartOne ▽¬≡(↥⊃(/=⊏0_2)(/=⊏1_3)).Data
