Solve ⇐ {env‿part 𝕊 line :
  util‿⟨hashset⟩ ← •Import¨ "/util.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data ← >{[⟨1⊑𝕩,0,0,0⟩,⟨2⊑𝕩,0,0,0⟩,⟨3⊑𝕩,4⊑𝕩,0,0⟩,⟨5⊑𝕩,0,6⊑𝕩,0⟩]}∘util.ParseInts¨line
  Examine ← {u 𝕊 n :
    best‿bp‿upto ← ⟨0,n⊏data,-u⟩
    masks‿limits ← ⟨0<˘bp,0‿0‿0‿∞⌈⌈´˘⍉bp⟩
    Expand ← {𝕊 cands :
      # Minimize ← {e 𝕊 list : bad ← (∧´e⊸≥)¨list ⋄ ⟨e⟩∾(¬bad)/list}
      util.Progress⟨n,best,≠cands⟩
      ∧{𝕩.Values⁼@}(Hashset⟨⟩){time‿resources‿robots 𝕊 hash :
          {
            upto< t ← time- w ← 1+⌈⌈´(𝕩⊏masks)/robots÷˜(no ← 𝕩⊏bp)(0⌈-)resources ?
            new ← t∾(no-˜resources+w×robots)∾((1⊸+)⌾(𝕩⊸⊑)robots)
            ¬hash.Has new ? hash.Set new ⋄ best ((4⊑new)+(t-upto)×¯1⊑new)⊸⌈ ↩ ; @
            # ¬∨´(∧´new⊸≤)¨next ? next ⟨new⟩⊸∾ ↩ ⋄ best ((4⊑new)+(t-upto)×¯1⊑new)⊸⌈ ↩ ; @
          }¨{robots<○(𝕩⊸⊑)limits}¨⊸/↕4
          # util.Debug hash.
          hash
      }´{⟨⊑𝕩,4↑1↓𝕩,5↓𝕩⟩}¨cands
    }
    Expand•_while_(⟨⟩⊸≢)⟨⟨0⟩∾⟨0,0,0,0⟩∾⟨1,0,0,0⟩⟩
    best
  }
  {1=part ? +´24((1⊸+)×Examine)¨↕≠data ; ×´32 Examine¨↕3}
}
