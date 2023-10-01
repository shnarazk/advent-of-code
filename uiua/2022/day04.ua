data ← ⊜□≠@\n.&fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day04.txt"
data ← ∵(|1 ⊜parse¬∊∶"-," .!)data
FullyContains ← ↥↧≥↷≥↶;⍥(↘¯1∶⊡¯1.)4∶↧≤↷≤↶;⍥(↘¯1∶⊡¯1.)4.
~~~
⍤"0_9 should fully contain 2_3" FullyContains 0_9_2_3
⍤"3_4 should is fully contained in 0_9" FullyContains 3_4_0_9
⍤"0_3 should not is fully contained in 5_8" ¬ FullyContains 0_3_5_8
~~~
/+≡FullyContains data
