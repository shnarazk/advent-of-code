Solve ⇐ {env‿part 𝕊 data : 
  util ← •Import "/util.bqn"∾˜ "." env.Var⌾⋈ "BQN_LIB"
  segments ← util.ParseInt¨¨", ->"⊸util.Split¨data
  Seq ← {(<⊑¨𝕩)+{(<×𝕩)×↕1+⌈´|𝕩}·-˜´¨𝕩}·<˘·⍉>
  # !⟨4‿0,4‿1,4‿2⟩     ≡ "seq1" util.Debug Seq ⟨4,0⟩‿⟨4,2⟩
  # !⟨3‿1,2‿1,1‿1,0‿1⟩ ≡ "seq2" util.Debug Seq ⟨3,1⟩‿⟨0,1⟩
  # !⟨1‿1,2‿2,3‿3⟩     ≡ "seq3" util.Debug Seq ⟨1,1⟩‿⟨3,3⟩
  # !⟨3‿3,2‿2,1‿1⟩     ≡ "seq4" util.Debug Seq ⟨3,3⟩‿⟨1,1⟩
  # !⟨1‿9,2‿8,3‿7⟩     ≡ "seq5" util.Debug Seq ⟨1,9⟩‿⟨3,7⟩
  {
    1=part ? +´1=⊒∾Seq¨⥊⥊<˘∘‿2⥊<˘∘‿2⥊∾{x1‿y1‿x2‿y2 : (x1=x2)∨(y1=y2)}¨⊸/segments ;
    +´1=⊒∾Seq¨⥊⥊<˘∘‿2⥊<˘∘‿2⥊∾segments
  }
}
