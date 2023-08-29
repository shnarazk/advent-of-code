Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨"." env.Var○< "BQN_LIB"
  "goal" util.Debug goalIndex ← ¯1+ shape ← 4+(1+2×numKinds ← {1=part ? 5 ; 7})↑0
  initIndex ← {1=part ? ⟨0,0,0,0,0,1,2,1,1,1,1⟩ ; ⟨0,0,0,0,0,1,2,1,1,1,1,0,0,0,0⟩}
  !goalIndex≡○≢initIndex
  IsSafe ← {
         F state : ∧´state⊸(F˜)¨↕numKinds ;
    kind F state :
      generator‿chip ← (1‿2+2×kind)⊏state
      otherGenerators ← (1+2×kind⊸≠⊸/↕numKinds)⊏state
      (generator=chip)∨(¬<⁼chip∊otherGenerators)
  }
  ValidMove ← {(𝕨≢𝕩)∧2≥+´𝕨≠𝕩}
  NextStates ← {F state :
    ⟨elevator⟩‿objects ← 1(↑⋈↓)state
    nextFloors ← (0⊸≤∧4⊸>)¨⊸/¯1‿1+elevator
    IsSafe¨⊸/⍷∾{
      floors ← elevator‿𝕩
      ⟨𝕩⟩<⊸(∾¨)objects⊸ValidMove¨⊸/⟨⟨⟩⟩{elevator=𝕨 ? ⥊floors∾⌜𝕩 ; ⥊⟨𝕨⟩∾⌜𝕩}´objects
    }¨nextFloors
  }
  (initIndex HashMap○⋈ 0){h 𝕊 n:
    !0<≠s ← ∾NextStates∘⊑¨(n=1⊸⊑)¨⊸/h.Values⁼˜@
    util.Progress ⟨1+n, ≠s⟩
    (1+n){𝕨 < ∞ h.Get 𝕩 ? 𝕩 h.Set 𝕨 ; @}¨s
    1+n
  }•_while_{¬𝕨.Has goalIndex}0
}
