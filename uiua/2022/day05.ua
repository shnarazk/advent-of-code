data ← &fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day05.txt"
ParseInts ← (|1 ⊜parse∊∶"0123456789-".!)
head ← ⊜□≠@\n.!⍘⊟⊜□¬⊂∶0⌕"\n\n".data
♭≡(□+0_¯1_¯1 ParseInts)⊜□≠@\n.!
moves ← 
towers ← ≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡!↘¯1 head
# transform 0 {"abce" "" "xy"} 2_0_2 → ["ce", "", "baxy"]
Move ← (
  →!→∶
  →→→(∵⧻.⊏)→(.⊃⊢(↘1)) →→∶→∩.
  →→(∧(⊂→!)[]⊂⊓(□⍛1↙∶[])(□⍛2↙∶[])⍘⊟+× ¯1_0)
  →(⊂⍛0↙∶[])
  →→(/'⊂∩!)
  →(↙3⊂∶□""⊂∶□"" ⊕□)
  →;⍜⊏^→'↘1□⍜(⊡1)(□⊂∩!∶)∶⊃'⊡0'↘1 ?(⍜(⊡0)·)(⍜(⊡0)⇌)
)

&p$"Part1: _"≡(|1 ⊢!)∧(Move 0) towers moves
&p$"Part2: _"≡(|1 ⊢!)∧(Move 1) towers moves
