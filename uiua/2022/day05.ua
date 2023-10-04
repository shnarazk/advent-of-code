data ← &fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day05.txt"
ParseInts ← (|1 ⊜parse∊∶"0123456789-".!)
⊜□≠@\n.!⍘⊟⊜□¬⊂∶0⌕"\n\n".data
head ← 
♭≡(□+0_¯1_¯1 ParseInts)⊜□≠@\n.!
moves ← 
≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡!↘¯1 head
towers ← 

Unfold ← (|1 /·⇌)
Split ← ⍘⊟↙2⊂∶[□""]⊜□+1≥∶⇡∶→(⧻.)
# I gave up the Under-based array modification. Instead use `rotate⁼ join drop rotate`
# Reshape was deprecated!!
# The best approach to handle this complexity may be packing all arguments
# into a list, say, arsenal.
# Now you can pick any number of arguments for each step from the arsenal
# by calling `select` once. 

# 2 0_2 {"abce" "" "xy"}
# →→→(∵⧻.⊏)∶→∶.→.→→.
# →→(+× ¯1_0)
# →→(\+∧(⊂→!)[]∵(□=0⇡))
# →(⊂⍛2↙∶[])
# →→/⊂
# →→(/(⊂∷!))
# →(↘1⊕□)
# ⍜⊏^ ∶
# →;

Move ← (|3
  # STACK: modifier towers move
  /!⍥'⊂→□ 2□
  Unfold!
  # STACK: pickup from to towers modifiers
  ⇵[1 3 0 2 3 4 3 1 2]
  # STACK: from towers pickup to towers modifiers towers from to
  ∶∷!Split∶!⊡
  # STACK: leftover moving to towers modifiers towers from to
  →→'!⊡
  # STACK: leftover moving target modifiers towers from to
  ⇵ [0 3 1 2]
  # STACK: leftover modifiers moving target towers from to
  →(|3 ∶⊂!)
  # STACK: leftover towers target' from to
  ⇵[1 3 0 3 4 2 4]
  # STACK: towers from leftover from to target' to
  ⍥(↻¯∶⊂□∶↘1↻∶)2
)
&p$"Part1: _"≡(|1 ⊢!)∧(Move(⇌)) towers moves
&p$"Part2: _"≡(|1 ⊢!)∧(Move(·)) towers moves
