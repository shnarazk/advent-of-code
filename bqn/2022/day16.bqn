#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap,While⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
data ← ∧(Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16.txt" DataFile •args
nodes ← ⍷⊑¨data
! 0=⊑nodes⊐<"AA"
pairs ← {𝕊 ⟨a,b⟩: ⟨⊑nodes⊒<a,⊑nodes⊒<b⟩}¨∾(⊏(∾○<)¨(2⊸↓))¨data
dist ← (⌊˝∘+⎉1‿∞)⍟(≠nodes)˜ {𝕨≡𝕩 ? 0; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
To_visit ← (>○⊑)_to_heap
to_visit.Push initial_state ← <⟨0, 0, 0, (0⊸=)¨↕≠nodes⟩ 
visited ← ∘‿2⥊⟨⟨0, 0, 3⊑⊑initial_state⟩, 0⟩ # is a map from ⟨time, location, map⟩ to flow
Expand ← {limit F ⟨flow, time, pos, states⟩:
  {F ⟨next_pos,cost⟩:
    new_time ← 1+time+cost
    {(0=cost)∨(next_pos⊑states)∨(limit≤new_time)∨(0=1⊑next_pos⊑data) ?@;
      new_flow ← flow + (limit-new_time)×1⊑next_pos⊑data
      new_states ← 1˙⌾(next_pos⊸⊑)states
      key ← ⟨new_time,next_pos,new_states⟩
      key_index ← ⊑(⊑˘visited)⊐⟨key⟩
      {key_index<≠visited ?@; visited (∾⟜(∘‿2⥊⟨key,0⟩))↩} # ensure the key exists
      {new_flow ≤ ⌈´(({(new_time≥⊑𝕩)∧(key ≡○(1↓⊑) 𝕩)}∘⊑)¨)⊸/⟜((1⊸⊑)¨)⥊<˘visited ?@;
        visited ↩ new_flow˙⌾(key_index‿1⊸⊑) visited
        to_visit.Push<⟨new_flow,new_time,next_pos,new_states⟩
      }
    }
  }¨ ((↕≠)⋈¨⊢) pos⊏dist
}
Serch ← {F limit:
  cand ← 0
  While {𝕤⋄ ¬to_visit.Empty @}‿{𝕤⋄ state ← to_visit.Pop @⋄ cand ↩ cand⌈⊑state⋄ limit Expand state}
  cand
}
•Show Serch 30
