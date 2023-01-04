#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap,While⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
data ← (Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16-0.txt" DataFile ⟨⟩ # •args
nodes ← ∧⍷⊑¨data
! 0=⊑nodes⊐<"AA" # Product ← +˝∘×⎉1‿∞
label_pairs ← ∧∾(⊏(∾○<)¨(2⊸↓))¨data
pairs ← {𝕊 ⟨a,b⟩: ⟨⊑nodes⊒<a,⊑nodes⊒<b⟩}¨label_pairs
dist ← (⌊˝∘+⎉1‿∞)⍟(≠nodes)˜ {𝕨≡𝕩 ? 0; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
To_visit ← (<○⊑)_to_heap
to_visit.Push initial_state ← <⟨0, 0, 0, (0⊸=)¨↕≠nodes⟩
visited ← ⟨initial_state⟩
Expand ← {limit F ⟨time, flow, pos, states⟩:
  {F ⟨next_pos,cost⟩:
    {(next_pos=pos)∨(next_pos⊑states)∨(limit<time+cost) ? @;
      new_time ← 1+time+cost
      gain ← (limit-new_time)×1⊑next_pos⊑data
      new ← <⟨new_time,flow+gain,next_pos,1˙⌾(next_pos⊸⊑)states⟩
      {visited(⊑∊)˜⟨new⟩ ? @; visited (⟨new⟩⊸∾)↩⋄  to_visit.Push new}
    }
  }¨ ((↕≠)⋈¨⊢) pos⊏dist
}
Serch ← {F limit: 
  cands ← ⟨0⟩
  While {𝕤⋄ ¬to_visit.Empty @}‿{𝕤⋄ state ← to_visit.Pop @⋄ cands ↩ ⍷(1⊑state)∾cands⋄ limit Expand state}
  cands
}
•Show ⊑∨ Serch 8
