Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "goal" util.Debug goalIndex ← ¯1+ shape ← 4+{1=part ? 11 ; 15}↑0
  initIndex ← {1=part ? ⟨0,0,0,0,0,1,2,1,1,1,1⟩ ; ⟨0,0,0,0,0,1,2,1,1,1,1,0,0,0,0⟩}
  "v" util.Debug ≢v ← ∞¨↕shape
  numKinds ← {1=part ? 2 ; 4}
  v 0⌾(initIndex⊸⊑) ↩
  !∞=goalIndex⊑v
  IsSafe ← {
         F state : ∧´state⊸(F˜)¨↕numKinds ;
    kind F state :
      generator‿chip ← (1‿2+2×kind)⊏state
      otherGenerators ← (1+2×kind⊸≠⊸/↕numKinds)⊏state
      (generator=chip)∨(¬<⁼chip∊otherGenerators)
  }
  ValidMove ← {a 𝕊 b : (a≢b)∧2≥+´a≠b }
  NextStates ← {F state :
    ⟨elevator⟩‿objects ← 1(↑⋈↓)state
    nextFloors ← (0⊸≤∧4⊸>)¨⊸/¯1‿1+elevator
    IsSafe¨⊸/⍷∾{floors ← elevator‿𝕩 ⋄ ⟨𝕩⟩<⊸(∾¨)objects⊸ValidMove¨⊸/⟨⟨⟩⟩{elevator=𝕨 ? ⥊floors∾⌜𝕩 ; ⥊⟨𝕨⟩∾⌜𝕩}´objects}¨nextFloors
  }
  {𝕊 n:
    util.Progress n
    s ← ∾NextStates¨(n=⊑⟜v)¨⊸/⥊↕≢v
    !0<≠s
    {v (n+1)⊸⌊⌾(𝕩⊸⊑) ↩}¨s
    1+n}•_while_{𝕤⋄ ∞=goalIndex⊑v}0
}
