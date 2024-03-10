Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data "0123456789ABCDEF"⊸⊐⌾⋈¨∘⊑ ↩
  len ← ≠data (∾{⌽4↑8‿1•bit._cast⋈𝕩}¨) ↩
  Version ← 3⊸↑
  TypeID ← 3⊸↑3⊸↓
  ToNum ← {0{+⟜(2⊸×)}´⌽𝕩}
  sum ← 0
  num_packets_stack ← ⟨0⟩
  value_stack ← ⟨⟨⟩⟩
  Traverse ← {𝕊 start :
    ¬∧´0=start↓data ?
    num_packets_stack (1⊸+⌾⊑) ↩
    packet ← start↓data
    "# start" util.Debug start⋈6↑packet
    sum + ↩ version ← ToNum Version packet
    type ← ToNum TypeID packet
    {
      4=type ?
        blocks ← <˘⌽‿5⥊6↓packet
        len ← 1+(⊑¨blocks)⊸⊐⌾⋈0
        payload ← ToNum∾1⊸↓¨len↑blocks
        value_stack (payload⊸∾⌾⊑) ↩
        start+6+5×len
      ;
        num_packets_stack ⟨0⟩⊸∾ ↩
        value_stack ⟨⟨⟩⟩⊸∾ ↩
        lengthTypeID ← 6⊑packet
        length_indicator ← ToNum lengthTypeID◶⟨15⊸↑,11⊸↑⟩7↓packet
        r ← {
          0=lengthTypeID ?
            limit ← length_indicator+22+start
            Traverse•_while_(limit⊸>)22+start
          ;
            Traverse•_while_{𝕤 ⋄ length_indicator>⊑num_packets_stack}18+start
        }
        num_packets_stack 1⊸↓ ↩
        val ← type◶⟨+´,×´,⌊´,⌈´,⊢,<´,>´,=´⟩⊑value_stack
        value_stack (val⊸∾⌾⊑1⊸↓) ↩
        r
    }
    ;
    S 𝕩 : ≠data
  }
  Traverse•_while_(len⊸>)0
  {1=part ? sum ; ⊑⊑value_stack}
}
