Solve ⇐ {env‿part 𝕊 data :
  util‿⟨longlist⟩ ← •Import¨"/util.bqn"‿"/longlist.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInt∘⊑ ↩
  storage ← LongList 120000
  storage.Add¨3‿7
  {
    1=part ?
      Process ← {indexes‿storage :
        {0=1000|len ← storage.Size@ ? util.Progress len ; @}
        storage.Add¨util.Digits+´ current ← storage.Get¨indexes
        ⟨(storage.Size@)|indexes+1+current,storage⟩
      }
      {10↑data↓∾𝕩.vec}1⊑Process•_while_{(10+data)>(1⊑𝕩).Size@}⟨0‿1,storage⟩
    ;
      l ← 1+ k ← ≠ data util.Digits ↩
      d ← ⋈¯1⊑data
      !(⊑d)≠¯2⊑data
      Process ← {indexes‿storage‿to_check :
        {0=10000|len ← storage.Size@ ? util.Progress len ; @}
        storage.Add¨ dd ← util.Digits+´ current ← storage.Get¨indexes
        ⟨(storage.Size@)|indexes+1+current,storage,dd∊d⟩
      }
      Shape ← {((1⊑𝕩).Size@)-((1‿0⊸≢∨1‿1⊸≢)2⊑𝕩)◶⟨⊢,1⊸+⟩k}
      Check ← {n‿storage‿check :
        {
           0‿0 : 1 ;
           0‿1 : data≢storage.Tail k ;
           1‿x : data≢¯1↓storage.Tail l ;
           ⟨0⟩ : 1 ;
           ⟨1⟩ : data≢storage.Tail k
        }check
      }
      Shape Process•_while_ Check ⟨0‿1,storage,⟨0⟩⟩
  }
}
