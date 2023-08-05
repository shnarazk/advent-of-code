Solve ⇐ {env‿part 𝕊 data :
  lib ← "." env.Var⌾⋈ "BQN_LIB"
  util‿⟨HashMap⟩‿⟨HashSet⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"∾˜¨<lib
  "# shapes" util.Debug shapes ← [
    shape0 ← <[1‿1‿1‿1]
    shape1 ← <[0‿1‿0,1‿1‿1,0‿1‿0]
    shape2 ← <[0‿0‿1,0‿0‿1,1‿1‿1]
    shape3 ← <[⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩]
    shape4 ← <[1‿1,1‿1]
  ]
  _in_ ← {𝕨 𝔽 _𝕣_ 𝔾 𝕩 : diff ← 𝕨-○(𝕗⊸⊑)𝕩 ⋄ ((diff≥⊣)∧(diff≤⊢))´𝕘}
  ! 0‿0 (0)_in_(¯2‿2) 1‿0
  Clashes ← {
    0‿(y‿x) 𝕊 ⟨⟩    : (0>x)∨(3<x) ;
    1‿(y‿x) 𝕊 ⟨⟩    : (0>x)∨(4<x) ;
    2‿(y‿x) 𝕊 ⟨⟩    : (0>x)∨(4<x) ;
    3‿(y‿x) 𝕊 ⟨⟩    : (0>x)∨(6<x) ;
    4‿(y‿x) 𝕊 ⟨⟩    : (0>x)∨(5<x) ;
    0‿pos1 𝕊 0‿pos2 : (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯3,3⟩pos2) ;
    0‿pos1 𝕊 1‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨0,2⟩pos2)∧(pos1(1)_in_⟨¯2,1⟩pos2)     #horizontal-to-vertical
          (pos1(0)_in_⟨1,1⟩pos2)∧(pos1(1)_in_⟨¯3,2⟩pos2)     # horizontal bars
        ⟩
      ;
    0‿pos1 𝕊 2‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯3,2⟩pos2)     # horizontal bars
          (pos1(0)_in_⟨0,2⟩pos2)∧(pos1(1)_in_⟨¯1,2⟩pos2)     # horizontal-to-vertical
        ⟩
      ;
    0‿pos1 𝕊 3‿pos2 : (pos1(0)_in_⟨0,3⟩pos2)∧(pos1(1)_in_⟨¯3,0⟩pos2) ;
    0‿pos1 𝕊 4‿pos2 :
        ∨´⟨
            (pos1(0)_in_⟨0,1⟩pos2)∧(pos1(1)_in_⟨¯3,0⟩pos2)   # horizontal-to-left_bar
            (pos1(0)_in_⟨0,1⟩pos2)∧(pos1(1)_in_⟨¯2,1⟩pos2)   # horizontal-to-right_bar
          ⟩
        ;
    1‿pos1 𝕊 1‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯2,2⟩pos2)      # horizontal bars
          (pos1(0)_in_⟨¯2,2⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2)      # vertical bars
          (pos1(0)_in_⟨¯1,1⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)     # horizontal-to-vertical and vice-veca
        ⟩
      ;
    1‿pos1 𝕊 2‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯1,¯1⟩pos2)∧(pos1(1)_in_⟨¯2,2⟩pos2)    # horizontal bars
          (pos1(0)_in_⟨¯2,2⟩pos2)∧(pos1(1)_in_⟨1,1⟩pos2)      # vertical bars
          (pos1(0)_in_⟨¯1,1⟩pos2)∧(pos1(1)_in_⟨0,2⟩pos2)      # horizontal-to-vertical
          (pos1(0)_in_⟨¯2,0⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)     # vertical-to-horizontal
        ⟩
      ;
    1‿pos1 𝕊 3‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯1,2⟩pos2)∧(pos1(1)_in_⟨¯2,0⟩pos2)     # horizontal-to-vertical
          (pos1(0)_in_⟨¯2,3⟩pos2)∧(pos1(1)_in_⟨¯1,¯1⟩pos2)    # vertical bars
        ⟩
      ;
    1‿pos1 𝕊 4‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨¯1,0⟩pos2)∧(pos1(1)_in_⟨¯2,0⟩pos2)     # horizontal-to-left_bar
          (pos1(0)_in_⟨¯1,0⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)     # horizontal-to-right_bar
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨¯1,¯1⟩pos2)    # vertical-to-left_bar
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2)      # vertical-to-right_bar
        ⟩
       ;
    1‿pos1 𝕊 0‿pos2 : 0‿pos2 𝕊 1‿pos1 ;
    2‿pos1 𝕊 2‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨0,0⟩pos2)∧(pos1(1)_in_⟨¯2,2⟩pos2)      # horizontal bars
          (pos1(0)_in_⟨¯2,2⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2)      # vertical bars
          (pos1(0)_in_⟨0,2⟩pos2)∧(pos1(1)_in_⟨0,2⟩pos2)       # horizontal-to-vertical
          (pos1(0)_in_⟨¯2,0⟩pos2)∧(pos1(1)_in_⟨¯2,0⟩pos2)     # vertical-to-horizontal
        ⟩
      ;
    2‿pos1 𝕊 3‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨0,3⟩pos2)∧(pos1(1)_in_⟨¯2,0⟩pos2)      # horizontal-to-vertical
          (pos1(0)_in_⟨¯2,3⟩pos2)∧(pos1(1)_in_⟨¯2,¯2⟩pos2)    # vertical bars
       ⟩
      ;
    2‿pos1 𝕊 4‿pos2 :
      ∨´⟨
          (pos1(0)_in_⟨0,1⟩pos2)∧(pos1(1)_in_⟨¯2,0⟩pos2)      # horizontal-to-left_bar
          (pos1(0)_in_⟨0,1⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2)      # horizontal-to-right_bar
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨¯2,¯2⟩pos2)    # vertical-to-left_bar
          (pos1(0)_in_⟨¯2,1⟩pos2)∧(pos1(1)_in_⟨¯1,¯1⟩pos2)    # vertical-to-right_bar
        ⟩
      ;
    2‿pos1 𝕊 0‿pos2 : 0‿pos2 𝕊 2‿pos1 ;
    2‿pos1 𝕊 1‿pos2 : 1‿pos2 𝕊 2‿pos1 ;
    3‿pos1 𝕊 3‿pos2 : (pos1(0)_in_⟨¯3,3⟩pos2)∧(pos1(1)_in_⟨0,0⟩pos2) ;
    3‿pos1 𝕊 4‿pos2 : (pos1(0)_in_⟨¯3,1⟩pos2)∧(pos1(1)_in_⟨0,1⟩pos2) ;
    3‿pos1 𝕊 0‿pos2 : 0‿pos2 𝕊 3‿pos1 ;
    3‿pos1 𝕊 1‿pos2 : 1‿pos2 𝕊 3‿pos1 ;
    3‿pos1 𝕊 2‿pos2 : 2‿pos2 𝕊 3‿pos1 ;
    4‿pos1 𝕊 4‿pos2 : (pos1(0)_in_⟨¯1,1⟩pos2)∧(pos1(1)_in_⟨¯1,1⟩pos2) ;
    4‿pos1 𝕊 0‿pos2 : 0‿pos2 𝕊 4‿pos1 ;
    4‿pos1 𝕊 1‿pos2 : 1‿pos2 𝕊 4‿pos1 ;
    4‿pos1 𝕊 2‿pos2 : 2‿pos2 𝕊 4‿pos1 ;
    4‿pos1 𝕊 3‿pos2 : 3‿pos2 𝕊 4‿pos1 ;
    𝕨‿𝕩!0
  }
  !1‿(2‿2) Clashes 2‿(4‿1)
  !2‿(4‿1) Clashes 1‿(2‿2)
  !2‿(3‿0) Clashes 1‿(2‿2)
  !¬2‿(4‿0) Clashes 1‿(2‿2)
  "# raw" util.Debug ⊑data
  "# wind" util.Debug jetPattern ← ¯1+2×'>'=⊑data
  memory_length ← 25
  Force ← 0⊸∾·jetPattern⊸(⊑˜)(≠jetPattern)⊸|
  Simulate ← {nth 𝕊 ground_level‿round‿record :
    rock ← shapes≠⊸|nth
    pos ← 1⊑{falling‿pos:
      pos ↩ pos+{¬∨´(rock⋈pos+𝕩)⊸Clashes¨(⟨⟨⟩⟩∾(-memory_length⌊≠)⊸↑record)}⊸×Force round    # drifting by wind
      round 1⊸+ ↩
      newpos ← ⟨¯1,0⟩+pos
      {
        ¬∨´rock‿newpos⊸Clashes¨((-memory_length⌊≠)⊸↑record) ? 0<⊑newpos ? 1‿newpos ;
        0‿pos
      }
    }•_while_⊑ 1‿⟨4+ground_level,2⟩
    # "new ground_level" util.Debug ⊑pos
    # "new record" util.Debug record∾<rock‿pos
    ⟨ground_level⌈-¬(⊑≢rock⊑shapes)+⊑pos,round,record∾<rock‿pos⟩
  }
  MetaSearch ← {@ :
    "≠jet" util.Debug ll ← ≠jetPattern
    "# ≠shapes" util.Debug ls ← ≠shapes
    ground_level‿round‿record ← 0‿0‿⟨⟩Simulate´⌽↕2×ll
    "occurs" util.Debug ¯40↑occur ← ⊒><∘((<·⋈⟜0·⊑⊑)-˜⊢)∘(1⊸⊑¨)˘⌊‿memory_length⥊record
    "not enough length holds in record"!∨´2=occur
    "cycle length" util.Debug len ← memory_length×+´1=occur
    "start at" util.Debug start ← 1+memory_length×+´0=occur
    "cycle tower base height" util.Debug cycle_base_height ← ⊑1⊑start⊑record
    "cycle tower height" util.Debug cycle_height ← ⊑-○(1⊸⊑⊑⟜record)´start+len‿0
    "unrational height"!(2-○{⊑⊑(start+𝕩×len)⊑record}1)=(3-○{⊑⊑(start+𝕩×len)⊑record}2)
    target ← 1000000000000-1
    util.Debug repeat ← len⌊∘÷˜target-start
    offset ← len|target-start
    "rock_type" util.Debug rock_type ← ⊑(start+offset)⊑record
    offset_height ← ⊑-○(1⊸⊑⊑⟜record)´start+offset‿0
    -¬(≠rock_type⊑shapes)+offset_height+cycle_base_height+repeat×cycle_height
  }
  {
    1=part ? ⊑0‿0‿⟨⟩Simulate´⌽↕2022 ; MetaSearch@
  }
}
