Solve ⇐ {env‿part 𝕊 data :
  lib ← "." env.Var⌾⋈ "BQN_LIB"
  util‿⟨HashMap⟩‿⟨HashSet⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<lib
  "shapes" util.Debug shapes ← [
    shape0 ← <[1‿1‿1‿1]
    shape1 ← <[0‿1‿0,1‿1‿1,0‿1‿0]
    shape2 ← <[0‿0‿1,0‿0‿1,1‿1‿1]
    shape3 ← <[⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩]
    shape4 ← <[1‿1,1‿1]
  ]
  _in_ ← {𝕨 𝔽 _𝕣_ 𝔾 𝕩 : diff ← 𝕨-○(𝕗⊸⊑)𝕩 ⋄ ((diff≥⊣)∧(diff≤⊢))´𝕘}
  ! 0‿0 (0)_in_(¯2‿2) 1‿0
  Clashes ← {
    0‿(y‿x) 𝕊 ⟨⟩    : (0≤x)∧(3<x) ;
    1‿(y‿x) 𝕊 ⟨⟩    : (0≤x)∧(4<x) ;
    2‿(y‿x) 𝕊 ⟨⟩    : (0≤x)∧(4<x) ;
    3‿(y‿x) 𝕊 ⟨⟩    : (0≤x)∧(6<x) ;
    4‿(y‿x) 𝕊 ⟨⟩    : (0≤x)∧(5<x) ;
    0‿pos1 𝕊 0‿pos2 : (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯3,3⟩pos2) ;
    0‿pos1 𝕊 1‿pos2 : (pos1(0)_in_⟨¯1,¯1⟩pos2)∧(pos1(1)_in_⟨¯2,3⟩pos2)∧(pos1(0)_in_⟨0,2⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2) ;
    0‿pos1 𝕊 2‿pos2 : (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯2,3⟩pos2)∧(pos1(0)_in_⟨¯2,¯2⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2) ;
    0‿pos1 𝕊 3‿pos2 : (pos1(0)_in_⟨0,3⟩pos2)∧(pos1(1)_in_⟨0,3⟩pos2) ;
    0‿pos1 𝕊 4‿pos2 : (pos1(0)_in_⟨0,1⟩pos2)∧(pos1(1)_in_⟨¯1,3⟩pos2) ;
    1‿pos1 𝕊 1‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯2,2⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2)      # vertical bars
          (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯2,2⟩pos2)      # horizontal bars
          (pos1(0)_in_⟨¯1,1⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)
        ⟩
      ;
    1‿pos1 𝕊 2‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯2,2⟩pos2)∧(pos1(1)_in_⟨¯1,¯1⟩pos2)    # vertical bars
          (pos1(0)_in_⟨1,1⟩pos2)∧(pos1(1)_in_⟨¯2,2⟩pos2)      # horizontal bars
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)     # vertical-to-horizontal
          (pos1(0)_in_⟨¯1,1⟩pos2)∧(pos1(1)_in_⟨¯2,0⟩pos2)     # horizontal-to-vertical
        ⟩
      ;
    1‿pos1 𝕊 3‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯2,3⟩pos2)∧(pos1(1)_in_⟨1,1⟩pos2)      # vertical bars
          (pos1(0)_in_⟨¯1,2⟩pos2)∧(pos1(1)_in_⟨0,2⟩pos2)      # horizontal-to-vertical
        ⟩
      ;
    1‿pos1 𝕊 4‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨1,1⟩pos2)      # vertical-to-left_bar
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2)      # vertical-to-right_bar
          (pos1(0)_in_⟨¯1,0⟩pos2)∧(pos1(1)_in_⟨0,2⟩pos2)      # horizontal-to-left_bar
          (pos1(0)_in_⟨¯1,0⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)     # horizontal-to-right_bar
        ⟩
       ;
    2‿pos1 𝕊 2‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯2,2⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2)      # vertical bars
          (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯2,2⟩pos2)      # horizontal bars
          (pos1(0)_in_⟨¯2,0⟩pos2)∧(pos1(1)_in_⟨0,2⟩pos2)      # vertical-to-horizontal
          (pos1(0)_in_⟨0,2⟩pos2)∧(pos1(1)_in_⟨¯2,0⟩pos2)      # horizontal-to-vertical
        ⟩
      ;
    2‿pos1 𝕊 3‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯2,3⟩pos2)∧(pos1(1)_in_⟨2,2⟩pos2)      # vertical bars
          (pos1(0)_in_⟨0,3⟩pos2)∧(pos1(1)_in_⟨0,2⟩pos2)       # horizontal-to-vertical
       ⟩
      ;
    2‿pos1 𝕊 4‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨2,2⟩pos2)      # vertical-to-left_bar
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨1,1⟩pos2)      # vertical-to-right_bar
          (pos1(0)_in_⟨0,1⟩pos2)∧(pos1(1)_in_⟨0,2⟩pos2)       # horizontal-to-left_bar
          (pos1(0)_in_⟨0,1⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)      # horizontal-to-right_bar
        ⟩
      ;
    3‿pos1 𝕊 3‿pos2 : (pos1(0)_in_⟨¯3,3⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2) ;
    3‿pos1 𝕊 4‿pos2 : (pos1(0)_in_⟨¯3,1⟩pos2)∧(pos1(1)_in_⟨¯1,0⟩pos2) ;
    4‿pos1 𝕊 4‿pos2 : (pos1(0)_in_⟨¯1,1⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2) ;
    𝕨 𝕊 𝕩 : 𝕩 𝕊 𝕨
  }
  jetPattern ← ¯1+2×'<'=⊑data
  Force ← 0⊸∾jetPattern⊸(⊑˜)(≠jetPattern)⊸|
  round ← 0
  Simulate ← {nth 𝕊 ground_level‿record :
    "next rock" util.Debug rock ← shapes≠⊸|nth
    pos ← 1⊑{falling‿pos:
      pos ↩ pos+(¬·∨´·record⊸(Clashes˜¨)·<rock⋈pos⊸+)⊸×Force round    # drifting by wind
      round 1⊸+ ↩
      newpos ← ⟨¯1,0⟩+pos
      {¬∨´(<rock‿newpos)Clashes¨record ? 0<⊑newpos ? 1‿newpos ; 0‿pos}
    }•_while_⊑ 1‿⟨4+ground_level,2⟩
    ⟨⊑pos,record∾<pos⟩
  }
  last ← 5
  # last ← 2022
  ⊑0‿⟨⟨⟩⟩Simulate´↕last
  0
}
