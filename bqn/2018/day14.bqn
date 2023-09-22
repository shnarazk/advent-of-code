Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  Digits ← {𝕊 𝕩 : ⟨⟩ 𝕊 𝕩 ; ⟨⟩ 𝕊 0 : ⟨0⟩ ; l 𝕊 0 : l ; (𝕨∾˜10|𝕩)𝕊 𝕩⌊∘÷10}
  !⟜(⟨0⟩⊸≡)Digits 0
  !⟜(⟨1,2,0⟩⊸≡)Digits 120
  LongList ← {
      chunk ← 𝕩
      vec ⇐ ⟨⟨⟩⟩
      Get ⇐ {𝕊 𝕩 : c ← 𝕩⌊∘÷chunk ⋄ (chunk|𝕩)⊑c⊑vec}
      Add ⇐ { chunk=≠¯1⊑vec ? vec ∾⟜⟨𝕩⟩ ↩ ; vec ∾⟜𝕩⌾(¯1⊸⊑) ↩ }
      Size ⇐ {𝕤 ⋄ +´≠¨vec}
      Tail ⇐ {
        𝕊 n : n≤Size@ ? (-n){ (-𝕨)≤≠𝕩 ? 𝕨↑𝕩 ; 𝕨↑∾⟜𝕩 ¯2⊑vec}¯1⊑vec ;
        𝕊 n : ∾vec
      }
  }
  # storage.Add¨ 1‿3‿5
  # "dump" util.Debug storage.vec
  # "get" util.Debug storage.Get¨ 0‿2‿1
  # "tail" util.Debug storage.Tail 2
  # "size" util.Debug storage.Size@
  storage ← LongList 100000
  storage.Add¨3‿7
  Process ← {indexes‿storage:
    {0=1000|len ← storage.Size@ ? util.Progress len ; @}
    dd ← Digits+´ current ← storage.Get¨indexes
    storage.Add¨dd
    ⟨(storage.Size@)|indexes+1+current,storage⟩
  }
  {
    1=part ?
      {10↑data↓∾𝕩.vec}1⊑Process•_while_{(10+data)>(1⊑𝕩).Size@}⟨0‿1,storage⟩
    ;
      l ← 1+ k ← ≠ data Digits ↩
      d ← ⋈¯1⊑data
      !(⊑d)≠¯2⊑data
      Process ← {indexes‿storage‿to_check :
        {0=10000|len ← storage.Size@ ? util.Progress len ; @}
        dd ← Digits+´ current ← storage.Get¨indexes
        storage.Add¨dd
        ⟨(storage.Size@)|indexes+1+current,storage,dd∊d⟩
      }
      Shape ← {((1⊑𝕩).Size@)-((1‿0⊸≢∨1‿1⊸≢)2⊑𝕩)◶⟨⊢,1⊸+⟩k}
      Check ← {
        storage ← 1⊑𝕩
        {
         0‿0: 1;
         0‿1: data≢storage.Tail k;
         1‿n: data≢¯1↓storage.Tail l;
         ⟨0⟩: 1;
         ⟨1⟩: data≢storage.Tail k;
          𝕩!0
        }2⊑𝕩
      }
      Shape Process•_while_ Check ⟨0‿1,storage,⟨0⟩⟩
  }
}
