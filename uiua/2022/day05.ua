data ← &fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day05.txt"
ParseInts ← (|1 ⊜parse∊∶"0123456789-".!)
head ← ⊜□≠@\n.!⍘⊟⊜□¬⊂∶0⌕"\n\n".data
♭≡(□+0_¯1_¯1 ParseInts)⊜□≠@\n.!
moves ← 
towers ← ≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉≡!↘¯1 head
# transform 0 {"abce" "" "xy"} 2_0_2 → ["ce", "", "baxy"]

FromArsenal ← (|3
  # build arsenal for under update
  [⊃⊃⊃(!⊡0)(⊡0!⊡2)(□↘1!⊡2)(⊡1)dump ⊂⊂⊙□]
  dump⊃⊃⊃(!!⊡1)(?((∘))((⇌))!⊡0)(∧(|2 ⊂⊙!)""⊏⊙(!⊡3)!⊡2.)∘
  dump⊂□⍜|'↙|
)

∧'FromArsenal0 towers ↙1moves
# /'FromArsenal2 [] # ↙2moves
