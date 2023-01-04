#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap,While⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
data ← (Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16-0.txt" DataFile ⟨⟩ # •args
nodes ← ∧⍷⊑¨data
! 0=⊑nodes⊐<"AA" # Product ← +˝∘×⎉1‿∞
label_pairs ← ∧∾(⊏(∾○<)¨(2⊸↓))¨data
pairs ← {𝕊 ⟨a,b⟩: ⟨⊑nodes⊒<a,⊑nodes⊒<b⟩}¨label_pairs
dist ← (⌊˝∘+⎉1‿∞)⍟(≠nodes)˜ { 𝕨≡𝕩 ? 0 ; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
To_visit ← (<○⊑)_to_heap
to_visit.Push<initial_state ← ⟨0, 0, 0, (0⊸=)¨↕≠nodes⟩
visited ← ⟨<initial_state⟩
ExpandState ← { limit F ⟨time, flow, pos, states⟩:
  {F ⟨next_pos,cost⟩:
    {(next_pos=pos)∨(next_pos⊑states)∨(limit<time+cost) ? @;
      ! 0<time+cost
      new ← ⟨time+cost,flow+1⊑next_pos⊑data,next_pos,1˙⌾(next_pos⊸⊑)states⟩
      # •Show visited
      {visited(⊑∊)˜⟨<new⟩ ? @; visited (⟨<new⟩⊸∾)↩⋄  to_visit.Push<new}
    }
  }¨ ((↕≠)⋈¨⊢) pos⊏dist
}
Traverse ← { limit F cands: 
  While {𝕤⋄ ¬to_visit.Empty @}‿{𝕤⋄ state ← to_visit.Pop @⋄ ! 0< ≠state⋄ cands ↩ ⍷(1⊑state)∾cands⋄ limit ExpandState state}
  cands
}
•Show ⊑∨ 26 Traverse ⟨0⟩
•Out "done"
