Solve ⇐ {env‿part 𝕊 rawdata :
  lib ← "." env.Var⌾⋈ "BQN_LIB"
  ⟨color,DataFile,Debug,ParseInts,Swap,term⟩ ← •Import lib∾"/util.bqn"
  ⟨_to_heap⟩‿⟨hashmap⟩ ← •Import¨(<lib)∾¨"/heap.bqn"‿"/hashmap.bqn"
  data ← ∧(Swap ParseInts ∾{((<1⊸⊑)∾9⊸↓)(','⊸≠¨⊸/)¨" "⊸((⊢-˜¬×·+`»⊸<)∘∊˜⊔⊢)𝕩})¨rawdata
  nodes ← ⍷⊑¨data
  ! 0=⊑nodes⊐<"AA"
  pairs ← (⋈○(⊑nodes⊒<))´¨∾(⊏(∾○<)¨(2⊸↓))¨data
  dist ← (⌊˝∘+⎉1‿∞)⍟(≠nodes)˜ {𝕨≡𝕩 ? 0 ; ⊑pairs∊˜⋈⟨𝕨,𝕩⟩ ? 1 ; ∞}⌜˜↕≠nodes
  {
    1=part ?
      To_visit ← (>○(¯1⊸⊑))_to_heap
      to_visit.Push⟨(0⊸=)¨↕≠nodes,0,0,0⟩   # heap of ⟨bitmap,position,time,flow⟩
      visited ← ∘‿2⥊⟨⟨(0⊸=)¨↕≠nodes,0,0⟩,0⟩ # map  of ⟨bitmap,position,time⟩→flow
      Expand ← { limit 𝕊 ⟨states,pos,time,flow⟩:
        {𝕊 ⟨p,cost⟩ :
          t ← 1+time+cost
          {(0=cost)∨(p⊑states)∨(limit≤t)∨(0=1⊑p⊑data) ? @ ;
            ⟨f,s⟩ ← ⟨flow+(limit-t)×1⊑p⊑data,1˙⌾(p⊸⊑)states⟩
            key_index ← ⊑(⊑˘visited)⊐⟨key ← ⟨s,p,t⟩⟩
            {key_index<≠visited ? @ ; visited (∾⟜(∘‿2⥊⟨key,0⟩)) ↩} # ensure the key exists
            {f≤⌈´(({(t≥2⊑𝕩)∧(key≡○(2↑⊑)𝕩)}∘⊑)¨)⊸/⟜((1⊸⊑)¨)⥊<˘visited ? @ ;
              to_visit.Push⟨s,p,t,f⟩
              visited f˙⌾(key_index‿1⊸⊑) ↩
            }
          }
        }¨(↕≠)⊸(⋈¨) pos⊏dist
      }
      Search ← {heap F lim : heap{state ← 𝕨.Pop@ ⋄ x ← 𝕩⌈¯1⊑state ⋄ lim Expand state ⋄ x}•_while_{¬𝕨.Empty@}0}
      to_visit Search 30
    ;
      limit ← 26
      Togo ← (>○(¯1⊸⊑))_to_heap
      togo.Push⟨(0⊸=)¨↕≠nodes,⟨0,0⟩,⟨0,0⟩,0⟩       # ⟨bitmap,⟨position1,time1⟩,⟨position2,time2⟩,flow⟩
      checked ← ⟨⟨(0⊸=)¨↕≠nodes,⟨0,0⟩,⟨0,0⟩⟩⟩ HashMap ⟨0⟩
      Expand2 ← { best‿limit 𝕊 ⟨states,⟨p1,t1⟩,⟨p2,t2⟩,flow⟩ :
        {𝕊 ⟨p,cost⟩ :
          t ← 1+t1+cost
          {(0=cost)∨(p⊑states)∨(limit≤t)∨(0=1⊑p⊑data) ? @ ;
            ⟨f,s⟩ ← ⟨flow+(limit-t)×1⊑p⊑data,1˙⌾(p⊸⊑)states⟩
            ⟨a,b⟩ ← {t<t2 ? ⟨⟨p,t⟩,⟨p2,t2⟩⟩ ; ⟨⟨p2,t2⟩,⟨p,t⟩⟩}
            length ← (¯1+limit-1⊑a)⌊≠remains ← ∨(¬¨s)/(1⊑¨data) # A* calculation
            {best<f++´remains×¨○(length⊸↑)⌽↕limit-t ? f>0 checked.Get key ← s‿a‿b ? togo.Push key∾⟨f⟩ ⋄ key checked.Set f ; @}
          }
        }¨(↕≠)⊸(⋈¨) p1⊏dist
      }
      togo{𝕨 𝕊 b :
        best ← 𝕩⌈3⊑state ← 𝕨.Pop@
        best‿limit Expand2 state
        best
      }•_while_{¬𝕨.Empty@}0
  }
}
