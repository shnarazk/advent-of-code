Data ← ⊜□≠@\n.&fras$"__Data_2022_input-day04.txt"&var"AOC_REPO_DIR" ..Sep
Data ← ∵(|1 ⊜parse¬∊∶"-,".⊔)Data
FullyContains ← ↥↧ ⊙≥∶⊙≤∶ ;⍥(↘¯1∶⊡¯1.)4∶↧ ⊙≤∶⊙≥∶ ;⍥(↘¯1∶⊡¯1.)4.
---
⍤"0_9 should fully contain 2_3" FullyContains 0_9_2_3
⍤"3_4 should is fully contained in 0_9" FullyContains 3_4_0_9
⍤"0_3 should not is fully contained in 5_8" ¬ FullyContains 0_3_5_8
---
&p$"Part1: _"/+≡FullyContains Data
CountOverlapped ← ↥0+1- ⊙↧∶⊙↥∶ ;⍥(↘¯1∶⊡¯1.)4
---
⍤"0_9 and 2_3 should have overlapped 2 pairs" =2 CountOverlapped 0_9_2_3
⍤"3_4 and 0_9 should have overlapped 2 pairs" =2 CountOverlapped 3_4_0_9
⍤"0_3 and 5_8 should have overladded 0 pairs" =0 CountOverlapped 0_3_5_8
---
&p$"Part2: _"/+>0≡CountOverlapped Data
