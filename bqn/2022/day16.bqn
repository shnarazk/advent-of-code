#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
data ← (Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16.txt" DataFile ⟨⟩ # •args
nodes ← ∧⍷⊑¨data
! 0=⊑nodes⊐<"AA" # Product ← +˝∘×⎉1‿∞
label_pairs ← ∧∾(⊏(∾○<)¨(2⊸↓))¨data
pairs ← {𝕊 ⟨a,b⟩: ⟨⊑nodes⊒<a,⊑nodes⊒<b⟩}¨label_pairs
# dist ← { 𝕨≡𝕩 ? 0 ; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
Distance ← ⌊˝∘+⎉1‿∞
dist ← Distance⍟(≠nodes)˜ { 𝕨≡𝕩 ? 0 ; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
# •Show 2⊏dist # ↩ dist Distance⍟(≠nodes) dist
To_visit ← (⊑∘⊑∘<)_to_heap
to_visit.Push<initial_state ← ⟨0, 0, 0, 0˙¨↕≠nodes⟩
visited ← ⟨⟩
cand ← ⟨⟩
ExpandState ← { F ⟨time, flow, pos, states⟩:
  # •Show "time"‿time
  next_poses ← ((↕≠)⋈¨⊢) pos⊏dist
  {F ⟨next_pos,cost⟩:
    # •Show "next_pos"‿next_pos
    # •Show "state"‿states
    {next_pos⊸⊑states ? @;
      new_states ← 1˙⌾(next_pos⊸⊑)states
      {⊑(<states)∊visited ? @;
        # TODO: visited (states⊸∾)↩
        # •Show time+cost
        to_visit.Push<⟨time+cost,flow+1⊑next_pos⊑data,next_pos,new_states⟩
      }
    }
  }¨ next_poses
  0
}
Traverse ← { F cands: 
  {to_visit.Empty @ ? cands;
    # •Show to_visit.Dump @
    state ← to_visit.Pop @
    # •Show "state"‿state
    # •Show 26⊸≤⊑state
    {26⊸≤⊑state ? cand (1⊑state⊸∾)↩ ;
      ExpandState state
    }
    Traverse cands
  }
}
•Show ⊑∨Traverse ⟨⟩