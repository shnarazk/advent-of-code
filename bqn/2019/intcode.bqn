# corresponds to day02
⟨config,run⟩ ⇐

env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
⟨hashmap⟩ ← •Import "/hashmap.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"

Config ← {(↕≠)⊸Hashmap 𝕩; ⊑1‿2 (𝕊 𝕩).Set¨ 𝕨}

Run ← {𝕊 m :
  {𝕊 ip :
    {
      1=𝕩 ? ops ← m.Get¨m.Get¨ip+1‿2 ⋄ (m.Get 3+ip)m.Set +´ops ⋄ ip 4⊸+ ↩ ;
      2=𝕩 ? ops ← m.Get¨m.Get¨ip+1‿2 ⋄ (m.Get 3+ip)m.Set ×´ops ⋄ ip 4⊸+ ↩ ;
      (ip⋈𝕩)!0
    }m.Get ip
    ip
  }•_while_(99≠m.Get)0
  m
}
