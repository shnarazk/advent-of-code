#!/usr/bin/env cbqn

Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  "goal" util.Debug goalIndex ← ¯1+ shape ← 4+{1=part ? 5 ; 9}↑0
  initIndex ← {1=part ? 0‿1‿0‿2‿0 ; 0‿1‿0‿2‿0‿0‿0‿0‿0}
  "v" util.Debug ≢v ← ∞¨↕shape
  numKinds ← {1=part ? 2 ; 4}
  v 0⌾(initIndex⊸⊑) ↩
  !∞=goalIndex⊑v
  # FIXME
  NextObjectsStates ← {F state :
    Mask ← {(¯2×numKinds)↑{ F 0 : ⟨0⟩ ; F n : {(F(n-𝕩)÷2)∾𝕩}2|n }𝕩}
    objects ← {(⊑𝕩)⊸=¨1↓𝕩}state
    blank ← 0˙¨1↓state
    indexes ← objects/⊢×⟜(↕∘≠)objects
    cands ← ⟨⟩
    {F i :
      cand ← 1˙⌾(i⊸⊑)blank
      { F j : i≤j ? cands∾↩ <1˙⌾(j⊸⊑)cand ; @}¨indexes
    }¨indexes
    cands
  }
  IsSafe ← {
         F state : ∧´state⊸(F˜)¨↕numKinds ;
    kind F state :
      generator‿chip ← (1‿2+2×kind)⊏state
      otherGenerators ← (1+2×kind⊸≠⊸/↕numKinds)⊏state
      (generator=chip)∨(¬<⁼chip∊otherGenerators)
  }
  # FIXME
  NextStates ← {F state :
    elevator ← ⊑state
    objects ← 1↓state
    nextFloors ← {(0≤𝕩)∧(𝕩<4)}¨⊸/⟨¯1+elevator,1+elevator⟩
    cands ← ⥊ nextFloors{𝕨∾((¬𝕩)×objects)+𝕨×𝕩}⌜NextObjectsStates state
    IsSafe¨⊸/cands
  }
  {𝕊 n: {v (n+1)⊸⌊⌾(𝕩⊸⊑) ↩}¨∾NextStates¨(n=⊑⟜v)¨⊸/⥊↕≢v ⋄ 1+n}•_while_{𝕤⋄ ∞=goalIndex⊑v}0
}
