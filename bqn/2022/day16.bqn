#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap,While⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
data ← (Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16.txt" DataFile •args
nodes ← ∧⍷⊑¨data
! 0=⊑nodes⊐<"AA" # Product ← +˝∘×⎉1‿∞
label_pairs ← ∧∾(⊏(∾○<)¨(2⊸↓))¨data
pairs ← {𝕊 ⟨a,b⟩: ⟨⊑nodes⊒<a,⊑nodes⊒<b⟩}¨label_pairs
dist ← (⌊˝∘+⎉1‿∞)⍟(≠nodes)˜ {𝕨≡𝕩 ? 0; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
To_visit ← (>○⊑)_to_heap
to_visit.Push initial_state ← <⟨0, 0, 0, (0⊸=)¨↕≠nodes⟩
# initialize   : d ← ∘‿2⥊∾{⟨<⟨𝕩,33⟩,0⟩}¨↕3
# add an itme  : d ((∘‿2⥊⟨<⟨88,55⟩,1⟩)⊸∾)↩
# update value : d ↩ 3˙⌾(2‿1⊸⊑) d
# contain key  : (⊑(⊑˘d)⊐⟨⟨1,¯1⟩⟩)<≠d
# access by key: (⊑(⊑˘d)⊐⟨⟨1,33⟩⟩)‿1⊑d
# visited is a map from ⟨current_location, current_time, visited_map⟩ to reward
visited ← ∘‿2⥊⟨⟨0, 0, 3⊑⊑initial_state⟩, 0⟩
Expand ← {limit F ⟨flow, time, pos, states⟩:
  {limit<time ?@;
    {F ⟨next_pos,cost⟩:
      {(next_pos⊑states)∨(limit≤1+time+cost)∨(0=1⊑next_pos⊑data) ?@;
        new_time ← 1+time+cost
        {0<1⊑next_pos⊑data ?@; •Show next_pos⊑data}
        ! 0<1⊑next_pos⊑data
        new_flow ← flow + (limit-new_time)×1⊑next_pos⊑data
        {flow = new_flow ?@;
          new_states ← 1˙⌾(next_pos⊸⊑)states
          key ← ⟨next_pos, new_time, new_states⟩
          key_index ← ⊑(⊑˘visited)⊐⟨key⟩
          {key_index<≠visited ?@; visited (∾⟜(∘‿2⥊⟨key,0⟩))↩} # ensure the key exists
          so_far ← ⌈´(({(key =○⊑ 𝕩)∧(new_time≥1⊑𝕩)∧(key ≡○(2⊸⊑) 𝕩)}∘⊑)¨)⊸/⟜((1⊸⊑)¨)⥊<˘visited
          {new_flow ≤ so_far ?@;
            visited ↩ new_flow˙⌾(key_index‿1⊸⊑) visited
            to_visit.Push<⟨new_flow,new_time,next_pos,new_states⟩

          }
        }
      }
    }¨ ((↕≠)⋈¨⊢) pos⊏dist
  }
}
Serch ← {F limit:
  cands ← ⟨0⟩
  While {𝕤⋄ ¬to_visit.Empty @}‿{𝕤⋄
    state ← to_visit.Pop @⋄
    {⊑state≥⌈´cands ? •Show 2↑state; @}
    cands ↩ ⍷(⊑state)∾cands⋄
    limit Expand state}
  cands
}
•Show ⊑∨ Serch 30
