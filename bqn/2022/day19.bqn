Solve ⇐ {env‿part 𝕊 line :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ← >{[⟨1⊑𝕩,0,0,0⟩,⟨2⊑𝕩,0,0,0⟩,⟨3⊑𝕩,4⊑𝕩,0,0⟩,⟨5⊑𝕩,0,6⊑𝕩,0⟩]}∘util.ParseInts¨line
  Examine ← {u 𝕊 n :
    round‿best‿bp‿upto ← ⟨0,0,n⊏data,-u⟩
    masks‿limits ← ⟨0<˘bp,0‿0‿0‿∞⌈⌈´˘⍉bp⟩
    {𝕊 prev :
      util.Progress⟨n,round,best,+´≠¨prev.Values@⟩
      round 1⊸+ ↩
      (Hashmap˜⟨⟩){robots‿value 𝕊 hash :
        {
          upto< t ← (⊑value)- w ← 1+⌈⌈´(𝕩⊏masks)/robots÷˜(no ← 𝕩⊏bp)(0⌈-) resources ← 1↓value ?
          rb‿v ← ⟨1⊸+⌾(𝕩⊸⊑)robots,⟨t⟩∾no-˜resources+w×robots⟩
          ¬∨´(∧´v⊸≤)¨vals ← ⟨⟩ hash.Get rb ?
          rb hash.Set ⟨v⟩∾(¬·∧´v⊸≥)¨⊸/vals
          best ((4⊑v)+(t-upto)×3⊑rb)⊸⌈ ↩
          ; @
        }¨{robots<○(𝕩⊸⊑)limits}¨⊸/↕4
        hash
      }´∾{𝕨⊸⋈¨𝕩}´¨prev.Values⁼˜@
    }•_while_{0<𝕩.Count@}⟨4↑1⟩Hashmap⟨⟨5↑0⟩⟩
    best
  }
  {1=part ? +´24((1⊸+)×Examine)¨↕≠data ; ×´32 Examine¨↕3}
}
