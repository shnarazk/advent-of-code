# corresponds to day02, 05, 07
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
⟨hashmap⟩ ← •Import "/hashmap.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
⟨running‿halt‿stop_by_input‿stop_by_output⟩ ⇐
# bit vector operations
statebits ← 8
TurnOn ← {𝕨 1‿1•bit._or 𝕩⌽statebits↑1}
TurnOff ← {𝕨 1‿1•bit._and 1‿1•bit._not 𝕩⌽statebits↑1}
Is ← (⊑˜)⟜(-¬)
running‿halt‿stop_by_input‿stop_by_output ⇐ ↕4

Intcode ⇐ {𝕩.Self𝕩}∘{
  Self⇐{self↩𝕩}
  ip ⇐ 0
  inputs ⇐ ⟨⟩
  outputs ⇐ ⟨⟩
  memory ⇐ (↕≠)⊸Hashmap 𝕩
  run_mode ← 8↑0 # 8↑⟨stop_at_input, stop_at_output⟩
  status ⇐ running       # 8↑(stopped_by_input, stopped_by_output)
  Config ⇐ {noun‿verb : 1‿2 memory.Set¨ noun‿verb ⋄ self}
  Get ⇐ {
    S 𝕩 : 1 𝕊 𝕩 ;
    0 𝕊 𝕩 : memory.Get memory.Get 𝕩 ;
    1 𝕊 𝕩 : memory.Get 𝕩}
  Set ⇐ memory.Set
  Mode ⇐ {𝕊 𝕩 : run_mode ↩ 8‿1•bit._cast⋈𝕩 ; 𝕊⁼ 𝕩 : run_mode}
  GetParam ← {𝕊 n :
    addrmode ← 10|(10⋆1+n)⌊∘(÷˜)memory.Get ip
    addrmode self.Get n+ip
  }
  SetParam ← {n 𝕊 𝕩 :
    (self.Get n+ip)self.Set 𝕩
  }
  Input ⇐ {𝕊⁼ 𝕩 : inputs ; 𝕊 𝕩 : inputs ↩ 𝕩 ⋄ self}
  Output ⇐ {
     𝕊  𝕩 : o ← outputs ⋄ output ↩ ⟨⟩ ⋄ o ;
   𝕨 𝕊  𝕩 : outputs ;
     𝕊⁼ 𝕩 : outputs ↩ 𝕩 ⋄ self
  }
  Run ⇐ {𝕊 c:
    {
      running=status ? @ ;
      (⟨⟩≢inputs)∧(run_mode Is stop_by_input) ?
        status ↩ running
        1 SetParam⊑inputs
        inputs 1⊸↓ ↩
        ip 2⊸+ ↩ ;
      (⟨⟩≡outputs)∧(run_mode Is stop_by_output) ?
        status ↩ running
        ip 2⊸+ ↩
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
            runmode Is stop_by_input ? ⟨⟩≡inputs ? status ↩ stop_by_input ;
            1 SetParam⊑inputs
            inputs 1⊸↓ ↩
            ip 2⊸+ ↩
          };
        4=op ?
          outputs ∾⟜(GetParam 1) ↩
          {runmode Is stop_by_output ? status ↩ stop_by_output ; ip 2⊸+ ↩};
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
