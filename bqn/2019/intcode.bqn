# corresponds to day02, 05
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
⟨hashmap⟩ ← •Import "/hashmap.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"

Intcode ⇐ {𝕩.Self𝕩}∘{
  Self⇐{self↩𝕩}
  ip ⇐ 0
  inputs ⇐ ⟨⟩
  outputs ⇐ ⟨⟩
  memory ⇐ (↕≠)⊸Hashmap 𝕩
  Config ⇐ {noun‿verb : 1‿2 memory.Set¨ noun‿verb ⋄ self}
  Get ⇐ {
    S 𝕩 : 1 𝕊 𝕩 ;
    0 𝕊 𝕩 : memory.Get memory.Get 𝕩 ;
    1 𝕊 𝕩 : memory.Get 𝕩}
  Set ⇐ memory.Set
  GetParam ⇐ {𝕊 n :
    mode ← 10|(10⋆1+n)⌊∘(÷˜)memory.Get ip
    mode self.Get n+ip
  }
  SetParam ⇐ {n 𝕊 𝕩 :
    (self.Get n+ip)self.Set 𝕩
  }
  Input ⇐ {𝕊⁼ 𝕩 : inputs ; 𝕊 𝕩 : inputs ↩ 𝕩 ⋄ self}
  Output ⇐ {𝕊 𝕩 : outputs ; 𝕊⁼ 𝕩 : outputs ↩ 𝕩 ⋄ self}
  Run ⇐ {𝕊:
    {𝕊 𝕩 :
      op ← 100|memory.Get ip
      {
        1=op ?
          3 self.SetParam+´self.GetParam¨1‿2
          ip 4⊸+ ↩ ;
        2=op ?
          3 self.SetParam×´self.GetParam¨1‿2
          ip 4⊸+ ↩ ;
        3=op ?
          1 self.SetParam⊑inputs
          inputs 1⊸↓ ↩
          ip 2⊸+ ↩ ;
        4=op ?
          outputs ∾⟜(self.GetParam 1) ↩
          ip 2⊸+ ↩ ;
        5=op ?
          ip (0≠self.GetParam 1)◶⟨3⊸+,self.GetParam 2⟩ ↩ ;
        6=op ?
          ip (0=self.GetParam 1)◶⟨3⊸+,self.GetParam 2⟩ ↩ ;
        7=op ?
          3 self.SetParam <´self.GetParam¨1‿2
          ip 4⊸+ ↩ ;
        8=op ?
          3 self.SetParam =´self.GetParam¨1‿2
          ip 4⊸+ ↩ ;
        ⟨ip,op⟩!0
      }
      @
    }•_while_{𝕤 ⋄ 99≠memory.Get ip}@
    self
  }
  ;
  1‿2(𝕊 𝕩).Set¨𝕨
}
