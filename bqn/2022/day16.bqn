#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
data ← (Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16.txt" DataFile ⟨⟩ # •args
•Show nodes ← ∧⍷⊑¨data
Product ← +˝∘×⎉1‿∞
Distance ← ⌊˝∘+⎉1‿∞
label_pairs ← ∧∾(⊏(∾○<)¨(2⊸↓))¨data
•Show pairs ← {𝕊 ⟨a,b⟩: ⟨⊑nodes⊒<a,⊑nodes⊒<b⟩}¨label_pairs
dist ← { 𝕨≡𝕩 ? 0 ; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
# •Show dist Distance⍟(≠nodes) dist
H ← <_to_heap
•Show h.Dump @
! 0=⊑nodes⊐<"AA"
•Show initial_state ← ⟨0, 0, 0, ↕≠nodes⟩
h.Push initial_state
visited ← ⟨⟩
Next ← { F ⟨time, flow, pos, states⟩:
  0
}

Expand ← { F heap: 
  ! ¬heap.Empty @ 
  state ← heap.Pop @
  { 26⊸≤⊑state ? state; Next state }
}
