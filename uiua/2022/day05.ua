Data ← &fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day05.txt"
ParseInts ← (|1 ⊜parse∊∶"0123456789-".!)
dump⊜□≠@\n.!⍘⊟⊜□¬⊂∶0⌕"\n\n".Data
Head ← 
♭≡(□+0_¯1_¯1 ParseInts)⊜□≠@\n.!
Moves ← 
dump≡(|1 □▽\↥≠@  .)▽=1◿4⇡⧻.⍉dump ≡'↘¯1 dump Head
Towers ← 
# transform 0 {"abce" "" "xy"} 2_0_2 → ["ce", "", "baxy"]

FromArsenal ← (|3
  # build arsenal for under update
  [⊃⊃⊃(!⊡0)(⊡0!⊡2)(□↘1!⊡2)(⊡1)dump ⊂⊂⊙□]
  dump⊃⊃⊃(?((∘))((⇌))!⊡0)(!!⊡1)(⊏⊙(!⊡3)!⊡2.)∘
  dump⊙⊙(|1.2 ⊡0.)
  dump⊙(⊃(↙dump!⊙'!!⍘⊟)(↘!⊙'!!⍘⊟)⊟∩□)
  dump⊂∩□ !
  dump⊂[⊃(⊡1)(□ ∧(|2 ⊂⊙!)""⊏0_2)]dump⊂⊙'↘1
  ;
)

∧'FromArsenal0 Towers ↙1Moves
# /'FromArsenal2 [] # ↙2Moves
