Solve ⇐ {env‿part 𝕊 line :
  util‿⟨hashmap⟩ ← •Import¨ "/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ← >{[⟨1⊑𝕩,0,0,0⟩,⟨2⊑𝕩,0,0,0⟩,⟨3⊑𝕩,4⊑𝕩,0,0⟩,⟨5⊑𝕩,0,6⊑𝕩,0⟩]}∘util.ParseInts¨line
  Examine ← {u 𝕊 n :
    best‿bp‿upto ← ⟨0,n⊏data,-u⟩
    masks‿limits ← ⟨0<˘bp,0‿0‿0‿∞⌈⌈´˘⍉bp⟩
    h ← ⟨⟨1,0,0,0⟩⟩Hashmap⟨⟨⟨0,⟨0,0,0,0⟩⟩,⟨1,⟨1,0,0,0⟩⟩⟩⟩
    true ← ⟨1,⟨1,1,1,1⟩⟩
    Expand ← {𝕊 cands :
      util.Progress⟨n,best,cands.Count@⟩
      (Hashmap˜⟨⟩){robots‿time‿resources 𝕊 hash :
        {
          upto< t ← time- w ← 1+⌈⌈´(𝕩⊏masks)/robots÷˜(no ← 𝕩⊏bp)(0⌈-)resources ?
          rb‿rs ← ⟨(1⊸+)⌾(𝕩⊸⊑)robots,no-˜resources+w×robots⟩
          v ← t‿rs
          ¬∨´(true≡v⊸≤)¨vals ← ⟨⟩ hash.Get rb ?
          rb hash.Set ⟨v⟩∾(¬true≡v⊸≥)¨⊸/vals
          best ((3⊑rs)+(t-upto)×3⊑rb)⊸⌈ ↩
          ; @
        }¨{robots<○(𝕩⊸⊑)limits}¨⊸/↕4
        hash
      }´∾{⟨𝕨⟩⊸∾¨𝕩}´¨{cands.Values⁼˜@}
    }
    Expand•_while_{0<𝕩.Count@}⟨⟨1,0,0,0⟩⟩Hashmap⟨⟨0⋈⟨0,0,0,0⟩⟩⟩
    best
  }
  {1=part ? +´24((1⊸+)×Examine)¨↕≠data ; ×´32 Examine¨↕3}
}
