Data ← ≡⊔-@0⊔⊜□≠@\n.&fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day08.txt"
# ⍚¯2□⇡.△↙ 8_8 Data

Split ← □⊂∩□⊃(|2 ⇌↙)(|2 ↘+1)
~~~
⍤ "Split"≅□[□[2 1 0] □[4 5]] Split 3 ⇡6
~~~
# ⍉∩≡(∺'Split∶ ∶⇡⧻.)⍉.Data
v ← ∵⍜∩⊔⊂ ⍉∩≡(∺'Split∶ ∶⇡⧻.)⍉.Data

# baseHeight listOfTree -- numberOfTrees
CheckSight ← ↧⊙⧻+1⊗1≥⊙⊔⊙'.⊔

# base dirs --- totalTree
CheckSights ← /×∺CheckSight ⊙⊔

/↥♭∵CheckSights Data v
