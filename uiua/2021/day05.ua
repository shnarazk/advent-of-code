Data ← ⊜□≠@\n.&fras $"__data_2021_input-day05.txt" &var"AOC_REPO_DIR" ..Sep

Ordered ← |2.2 ?⊙∘∶>,,
~~~
⍤ "ordered"≅ 0_1 ⊂ Ordered 1 0
⍤ "ordered"≅ 1_2 ⊂ Ordered 1 2
~~~

Line ← |1 ?(∺⊂⊙(+⊙(⇡+1-).Ordered)⊙⊙⋅∘)(⊙;∘∺'⊂∶⊙(+⊙(⇡+1-).Ordered)∶)⊃⊃⊃⊃(/=⊏0_2)(⊡0)(⊡1)(⊡2)(⊡3)
~~~
⍤ "line" ≅ [1_1 1_2 1_3] Line [1 1 1 3]
⍤ "line" ≅ [260_1 260_2 260_3] Line [260 1 260 3]
⍤ "line" ≅ [260_1 260_2 260_3 260_4] Line [260 4 260 1]
⍤ "line" ≅ [1_0 2_0 3_0] Line [1 0 3 0]
⍤ "line" ≅ [1_8 2_8 3_8] Line [1 8 3 8]
~~~

&p$"Part1: _"/+>1⍘⊚⊗∶⊝.∧(⊂⊙Line) ↯0_2[] ▽≡(↥⊃(/=⊏0_2)(/=⊏1_3)).∵(⊜parse¬∊," ,->"⊔)Data
