Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  {
    1=part ?
      "hex" util.Debug 20↑data "0123456789ABCDEF"⊸⊐⌾⋈¨∘⊑ ↩
      "bits" util.Debug ∘‿4⥊32↑data (∾{⌽4↑8‿1•bit._cast⋈𝕩}¨) ↩
      Version ← 3⊸↑
      TypeID ← 3⊸↑3⊸↓
      ToNum ← {0{+⟜(2⊸×)}´⌽𝕩}
      sum ← 0
      num_packets_stack ← ⟨0⟩

      Traverse ← {𝕊 start :
        ¬∧´0=start↓data ?
        num_packets_stack (1⊸+⌾⊑) ↩
        packet ← start↓data
        "start" util.Debug start⋈6↑packet
        sum + ↩ "version" util.Debug version ← ToNum Version packet
        type ← ToNum TypeID packet
        {
          4=type ?
            blocks ← <˘⌽‿5⥊6↓packet
            len ← 1+(⊑¨blocks)⊸⊐⌾⋈0
            payload ← ToNum∾1⊸↓¨len↑blocks
            start+6+5×len
            ;
          7≤≠packet ?
            num_packets_stack ⟨0⟩⊸∾ ↩
            lengthTypeID ← 6⊑packet
            length_indicator ← ToNum lengthTypeID◶⟨15⊸↑,11⊸↑⟩7↓packet
            "operator" util.Debug lengthTypeID‿length_indicator
            {
              0=lengthTypeID ?
                "subpacket bit limit" util.Debug limit ← length_indicator + 22 + start
                r ← Traverse•_while_(limit⊸>)22+start
                "stackdown" util.Debug num_packets_stack 1⊸↓ ↩
                r
              ;
                "subpacket number limit" util.Debug length_indicator
                r ← Traverse•_while_{𝕤 ⋄ length_indicator > ⊑num_packets_stack}18+start
                "stackdown" util.Debug num_packets_stack 1⊸↓ ↩
                r
            }
          ;
            !0
        }
        ;
        S 𝕩 : ≠data
      }
      len ← ≠data
      {𝕊 start : Traverse start}•_while_(len⊸>)0
      sum
    ;
    0
  }
}
