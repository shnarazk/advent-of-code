Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩‿⟨to_heap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"‿"/heap.bqn"∾˜¨"." env.Var○< "BQN_LIB"
  goalState ← ¯1+ 4+(1+2×numKinds ← {1=part ? 5 ; 7})↑0
  util.Debug vec ← 0∾{𝕊 name : <⁼1⊐˜{𝕊 line : ∨´name⊸≡˘(≠name)↕line}¨data}¨⟨
    "curium generator"   , "curium-compatible microchip"
    "plutonium generator", "plutonium-compatible microchip"
    "ruthenium generator", "ruthenium-compatible microchip"
    "strontium generator", "strontium-compatible microchip"
    "thulium generator"  , "thulium-compatible microchip"
⟩
  initState ← (2=part)◶⟨⊢,∾⟜0‿0‿0‿0⟩vec
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
  Estimate ← {cost 𝕊 state : cost+1.5⋆+´3-⌊´˘∘‿2⥊1↓state}    # distance to goal (smaller is better)
  To_visit ← (<○(¯1⊸⊑))_to_heap
  to_visit.Push(⋈∾0∾0⊸Estimate)initState
  min ← ∞
  {𝕩.Get goalState}{𝕊 visited :
    i‿s‿e ← to_visit.Pop@
    {e≤min ? util.Progress i‿s‿e⋄ min ↩ e ; @}
    (s+1){𝕨<∞ visited.Get 𝕩 ? 𝕩 visited.Set 𝕨 ⋄ to_visit.Push(⋈∾𝕨∾s⊸Estimate)𝕩 ; @}¨NextStates i
    visited
  }•_while_{¬𝕩.Has goalState}initState Hashmap○⋈ 0
}
