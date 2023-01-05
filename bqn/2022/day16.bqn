#!/usr/bin/env cbqn
⟨DataFile,ParseInts,Swap,While⟩ ← •Import "../lib.bqn"
⟨_to_heap⟩ ← •Import "../heap.bqn"
data ← ∧(Swap ParseInts∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨ •Flines "data/2022/input-day16.txt" DataFile •args
nodes ← ⍷⊑¨data
! 0=⊑nodes⊐<"AA"
pairs ← (⋈○(⊑nodes⊒<))´¨∾(⊏(∾○<)¨(2⊸↓))¨data
dist ← (⌊˝∘+⎉1‿∞)⍟(≠nodes)˜ {𝕨≡𝕩 ? 0; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1; ∞}⌜˜↕≠nodes
To_visit ← (>○(¯1⊸⊑))_to_heap
to_visit.Push<⟨(0⊸=)¨↕≠nodes,0,0,0⟩   # heap of ⟨bitmap,position,time,flow⟩
visited ← ∘‿2⥊⟨⟨(0⊸=)¨↕≠nodes,0,0⟩,0⟩ # map  of ⟨bitmap,position,time⟩→flow
Expand ← {limit 𝕊 ⟨states,pos,time,flow⟩:
  {𝕊 ⟨p,cost⟩:
    t ← 1+time+cost
    {(0=cost)∨(p⊑states)∨(limit≤t)∨(0=1⊑p⊑data) ?@;
      f ← flow + (limit-t)×1⊑p⊑data
      s ← 1˙⌾(p⊸⊑)states
      key_index ← ⊑(⊑˘visited)⊐⟨key ← ⟨s,p,t⟩⟩
      {key_index<≠visited ?@; visited (∾⟜(∘‿2⥊⟨key,0⟩))↩} # ensure the key exists
      {f ≤ ⌈´(({(t≥2⊑𝕩)∧(key ≡○(2↑⊑) 𝕩)}∘⊑)¨)⊸/⟜((1⊸⊑)¨)⥊<˘visited ?@;
        to_visit.Push<⟨s,p,t,f⟩
        visited ↩ f˙⌾(key_index‿1⊸⊑) visited
      }
    }
  }¨ ((↕≠)⋈¨⊢) pos⊏dist
}
Search ← {F limit:
  cand ← 0
  While {𝕤⋄ ¬to_visit.Empty @}‿{𝕤⋄ state ← to_visit.Pop @⋄ cand ↩ cand⌈¯1⊑state⋄ limit Expand state}
  cand
}
•Show Search 30

Togo ← (>○(¯1⊸⊑))_to_heap
togo.Push<⟨(0⊸=)¨↕≠nodes,⟨0,0⟩,⟨0,0⟩,0⟩       # ⟨bitmap,⟨position1,time1⟩,⟨pisition2,time2⟩,flow⟩
checked ← ∘‿2⥊⟨⟨(0⊸=)¨↕≠nodes,⟨0,0⟩,⟨0,0⟩⟩,0⟩ # ⟨bitmap,⟨position1,time1⟩,⟨pisition2,time2⟩⟩→flow
best ← 0
Expand2 ← {limit 𝕊 ⟨states,⟨p1,t1⟩,⟨p2,t2⟩,flow⟩:
  {𝕊 ⟨p,cost⟩:
    t ← 1+t1+cost
    {(0=cost)∨(p⊑states)∨(limit≤t)∨(0=1⊑p⊑data) ?@;
      f ← flow+(limit-t)×1⊑p⊑data
      s ← 1˙⌾(p⊸⊑)states
      ⟨a,b⟩ ← { t<t2 ? ⟨⟨p,t⟩,⟨p2,t2⟩⟩; ⟨⟨p2,t2⟩,⟨p,t⟩⟩}
      # calculation for A*
      remains ← ∨(¬¨s)/(1⊑¨data)
      length ← (¯1+limit-1⊑a)⌊≠remains
      {best≥f++´(length↑remains)×¨length↑⌽↕(limit-t)?@;
        key_index ← ⊑(⊑˘checked)⊐⟨key ← ⟨s,a,b⟩⟩
        {key_index<≠checked ?@; checked (∾⟜(∘‿2⥊⟨key,0⟩))↩}
        {f ≤ ⌈´(({(t≥1⊸⊑1⊸⊑𝕩)∧(t≥1⊸⊑2⊸⊑𝕩)∧(key ≡○(⊑) 𝕩)∧(key ≡○(⊑1⊸⊑) 𝕩)∧(key ≡○(⊑2⊸⊑) 𝕩)}∘⊑)¨)⊸/⟜((1⊸⊑)¨)⥊<˘checked ?@;
          togo.Push<⟨s,a,b,f⟩
          checked ↩ f˙⌾(key_index‿1⊸⊑) checked
        }
      }
    }
  } ¨ ((↕≠)⋈¨⊢) p1⊏dist
}
Search2 ← {F limit:
  While {𝕤⋄ ¬togo.Empty @}‿{𝕤⋄ state ← togo.Pop @⋄
    {best≤3⊸⊑state ? •Show ⟨3⊸⊑state,1⊸⊑1⊸⊑state⟩; @}
    best ↩ best⌈3⊸⊑state⋄ limit Expand2 state}
    best
}
•Show Search2 26
