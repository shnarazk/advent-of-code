#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap,While⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
nodes ← ⍷⊑¨data ← ∧(Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16.txt" DataFile •args
! 0=⊑nodes⊐<"AA"
pairs ← (⋈○(⊑nodes⊒<))´¨∾(⊏(∾○<)¨(2⊸↓))¨data
dist ← (⌊˝∘+⎉1‿∞)⍟(≠nodes)˜ {𝕨≡𝕩 ? 0; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
To_visit ← (>○⊑)_to_heap
to_visit.Push initial_state ← <⟨0, 0, 0, (0⊸=)¨↕≠nodes⟩ 
visited ← ∘‿2⥊⟨⟨0, 0, 3⊑⊑initial_state⟩, 0⟩ # is a map from ⟨time, location, map⟩ to flow
Expand ← {limit 𝕊 ⟨flow, time, pos, states⟩:
  {𝕊 ⟨p,cost⟩:
    t ← 1+time+cost
    {(0=cost)∨(p⊑states)∨(limit≤t)∨(0=1⊑p⊑data) ?@;
      f ← flow + (limit-t)×1⊑p⊑data
      s ← 1˙⌾(p⊸⊑)states 
      key_index ← ⊑(⊑˘visited)⊐⟨key ← ⟨t,p,s⟩⟩
      {key_index<≠visited ?@; visited (∾⟜(∘‿2⥊⟨key,0⟩))↩} # ensure the key exists
      {f ≤ ⌈´(({(t≥⊑𝕩)∧(key ≡○(1↓⊑) 𝕩)}∘⊑)¨)⊸/⟜((1⊸⊑)¨)⥊<˘visited ?@;
        to_visit.Push<⟨f,t,p,s⟩
        visited ↩ f˙⌾(key_index‿1⊸⊑) visited
      }
    }
  }¨ ((↕≠)⋈¨⊢) pos⊏dist
}
Search ← {F limit:
  cand ← 0
  While {𝕤⋄ ¬to_visit.Empty @}‿{𝕤⋄ state ← to_visit.Pop @⋄ cand ↩ cand⌈⊑state⋄ limit Expand state}
  cand
}
•Show Search 30
