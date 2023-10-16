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

Range ← ?(⍜¯(⇡+1))(⇡+1)<0.
~~~
⍤ "range" ≅ [0 1 2 3] Range 3
⍤ "range" ≅ [0 ¯1 ¯2 ¯3] Range ¯3
~~~

AllLine ← (|1 ⍉⊟⊃(+⊙(Range-).⊃'⊡0'⊡2)(+⊙(Range-).⊃'⊡1'⊡3))
~~~
⍤ "allline" ≅ [1_1 2_2 3_3] AllLine [1 1 3 3]
⍤ "allline" ≅ [260_4 261_3 262_2 263_1] AllLine [260 4 263 1]
~~~

Line ← |1 ?(∺⊂⊙(+⊙(⇡+1-).Ordered)⊙⊙⋅∘)(⊙;∘∺'⊂∶⊙(+⊙(⇡+1-).Ordered)∶)⊃⊃⊃⊃(/=⊏0_2)(⊡0)(⊡1)(⊡2)(⊡3)

PartOne ← ∧(⊂⊙Line) ↯0_2[] ▽≡(↥⊃(/=⊏0_2)(/=⊏1_3)).∵(⊜parse¬∊," ,->"⊔)Data
&p$"Part1: _"/+>1⍘⊚⊗∶⊝.PartOne
&p$"Part2: _"/+>1⍘⊚⊗∶⊝.∧(⊂⊙AllLine) PartOne ▽¬≡(↥⊃(/=⊏0_2)(/=⊏1_3)).∵(⊜parse¬∊," ,->"⊔)Data
