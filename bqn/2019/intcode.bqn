# corresponds to day02
# ⟨config,run⟩ ⇐

env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
⟨hashmap⟩ ← •Import "/hashmap.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"

Intcode ⇐ {𝕩.Self𝕩}∘{
  Self⇐{self↩𝕩}
  ip ⇐ 0
  inputs ⇐ ⟨⟩
  outputs ⇐ ⟨⟩
  memory ⇐ (↕≠)⊸Hashmap 𝕩
  Config ⇐ {noun‿verb : 1‿2 memory.Set¨ noun‿verb ⋄ self}
  Get ⇐ memory.Get
  Set ⇐ memory.Set
  Input ⇐ {𝕊 𝕩 : inputs ; 𝕊⁼ 𝕩 : inputs ↩ 𝕩}
  Output ⇐ {𝕊 𝕩 : outputs ; 𝕊⁼ 𝕩 : outputs ↩ 𝕩}
  Run ⇐ {𝕊:
    {𝕊 𝕩 :
      {
        1=𝕩 ?
          ops ← memory.Get¨memory.Get¨ip+1‿2
          (memory.Get 3+ip)memory.Set +´ops
          ip 4⊸+ ↩ ;
        2=𝕩 ?
          ops ← memory.Get¨memory.Get¨ip+1‿2
          (memory.Get 3+ip)memory.Set ×´ops
          ip 4⊸+ ↩ ;
        3=𝕩 ?
          ops ← memory.Get¨memory.Get¨ip+1‿2
          (memory.Get 3+ip)memory.Set ×´ops
          ip 4⊸+ ↩
        ;
        (ip⋈𝕩)!0
      }memory.Get ip
      @
    }•_while_{𝕤 ⋄ 99≠memory.Get ip}@
    self
  }
  ;
  1‿2(𝕊 𝕩).Set¨𝕨
}
