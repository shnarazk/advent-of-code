Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩‿⟨hashset⟩‿⟨to_heap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/hashset.bqn"‿"/heap.bqn"∾˜¨"." env.Var○< "BQN_LIB"
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
  # distance to goal (smaller is better)
  Estimate ← {cost 𝕊 state :
    cost++´4⋆˜2×3-state
    # cs ← 2⊸|¨≠state
    # gs ← ¬¨cs
    # dist ← 3-¨state
    # (2×+´1↓cs×dist)++´1↓gs×dist
  }
  {
    1=part ?
      (initIndex HashMap○⋈ 0){h 𝕊 n:
        !0<≠s ← ∾NextStates∘⊑¨(n=1⊸⊑)¨⊸/h.Values⁼˜@
        util.Progress ⟨1+n, ≠s⟩
        (1+n){𝕨 < ∞ h.Get 𝕩 ? 𝕩 h.Set 𝕨 ; @}¨s
        1+n
      }•_while_{¬𝕨.Has goalIndex}0 ;
    To_visit ← (<○(¯1⊸⊑))_to_heap
    to_visit.Push(⋈∾0∾0⊸Estimate)initIndex
    min ← ∞
    h ← {𝕊 visited :
      i‿s‿e ← to_visit.Pop@
      {e≤min ? util.Progress i‿s‿e⋄ min ↩ e ; @}
      {(s+1)<∞ visited.Get 𝕩 ? 𝕩 visited.Set s+1 ⋄ to_visit.Push(⋈∾(s+1)∾s⊸Estimate)𝕩 ; @}¨NextStates i
      visited
    }•_while_{¬𝕩.Has goalIndex}initIndex Hashmap○⋈ 0
    h.Get goalIndex
  }
}
