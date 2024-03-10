# corresponds to day02, 05, 07, 09, 11
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
⟨hashmap⟩ ← •Import "/hashmap.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
running‿halt‿awaiting ⇐ ↕3

Intcode ⇐ {𝕩.Self𝕩}∘{
  Self⇐{self↩𝕩}
  ip ⇐ 0
  relative_base ← 0
  inputs ⇐ ⟨⟩
  outputs ⇐ ⟨⟩
  memory ⇐ (↕≠)⊸Hashmap 𝕩
  status ⇐ running
  Config ⇐ {noun‿verb : 1‿2 memory.Set¨ noun‿verb ⋄ self}
  Get ⇐ {
    S 𝕩 : 1 𝕊 𝕩 ;
    0 𝕊 𝕩 : 0 memory.Get memory.Get 𝕩 ;
    1 𝕊 𝕩 : 0 memory.Get 𝕩 ;
    2 𝕊 𝕩 : !0≤a ← relative_base+memory.Get 𝕩 ⋄ 0 memory.Get a
  }
  Set ⇐ {
    0 𝕊 a‿x : a memory.Set x ;
    2 𝕊 a‿x : (relative_base+a) memory.Set x ;
    𝕨 𝕊 𝕩   : 𝕨 memory.Set 𝕩 ⋄ self
  }
  GetParam ← {𝕊 n :
    addrmode ← 10|(10⋆1+n)⌊∘(÷˜)memory.Get ip
    addrmode self.Get n+ip
  }
  SetParam ← {n 𝕊 𝕩 :
    addrmode ← 10|(10⋆1+n)⌊∘(÷˜)memory.Get ip
    addrmode self.Set (self.Get n+ip)‿𝕩
  }
  Input ⇐ {𝕊⁼ 𝕩 : inputs ; 𝕊 𝕩 : inputs ↩ 𝕩 ⋄ self}
  Output ⇐ {
     𝕊  𝕩 : o ← outputs ⋄ outputs ↩ ⟨⟩ ⋄ o ;
   𝕨 𝕊  𝕩 : outputs ;
     𝕊⁼ 𝕩 : outputs ↩ 𝕩 ⋄ self
  }
  Run ⇐ {𝕊 c:
    {
      running=status ? @ ;
      (⟨⟩≢inputs)∧(awaiting=status) ?
        1 SetParam⊑inputs
        inputs 1⊸↓ ↩
        ip 2⊸+ ↩
        status ↩ running ;
      @
    }
    {𝕊 𝕩 :
      op ← 100|memory.Get ip
      {
        1=op ?
          3 SetParam+´GetParam¨1‿2
          ip 4⊸+ ↩ ;
        2=op ?
          3 SetParam×´GetParam¨1‿2
          ip 4⊸+ ↩ ;
        3=op ?
          {
            ⟨⟩≡inputs ? status ↩ awaiting ;
            1 SetParam⊑inputs
            inputs 1⊸↓ ↩
            ip 2⊸+ ↩
          } ;
        4=op ?
          outputs ∾⟜(GetParam 1) ↩
          ip 2⊸+ ↩ ;
        5=op ?
          ip (0≠GetParam 1)◶⟨3⊸+,GetParam 2⟩ ↩ ;
        6=op ?
          ip (0=GetParam 1)◶⟨3⊸+,GetParam 2⟩ ↩ ;
        7=op ?
          3 SetParam <´GetParam¨1‿2
          ip 4⊸+ ↩ ;
        8=op ?
          3 SetParam =´GetParam¨1‿2
          ip 4⊸+ ↩ ;
        9=op ?
          relative_base +⟜(GetParam 1) ↩
          ip 2⊸+ ↩ ;
        99=op ?
          status ↩ halt ;
        ⟨ip,op⟩!0
      }
      @
    }•_while_{𝕤 ⋄ running=status}@
    self
  }
  ;
  1‿2(𝕊 𝕩).Set¨𝕨
}
