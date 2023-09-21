Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  initial‿rules ← 2(↑⋈↓)data
  rules '#'⊸=¨¨∘(" => "⊸util.Split)¨ ↩
  rules (⊑¨(⟨1⟩≡1⊸⊑)¨⊸/) ↩ # pick up only generators
  initial '#'⊸=∘(15⊸↓)∘⊑ ↩
  grow ← 4
  Extend ← {
    𝕊  g‿o‿v : ⟨g,o-4,(grow↑0){𝕨∾𝕩∾𝕨}v⟩ ;
    𝕊⁼ g‿o‿v : span ← (+´·×`0⊸=)v ⋄ ⟨g,o+span,(-·+´·×`·0⊸=⌽)⊸↓span↓v⟩
  }
  # !⟜(0‿6‿⟨0,0,0,0,1,0,0,0,0,0⟩⊸≡)Extend 0‿10‿⟨1,0⟩
  # !⟜(0‿9‿⟨1,0,0,1⟩⊸≡)Extend⁼ 0‿5‿⟨0,0,0,0,1,0,0,1,0⟩
  # !⟜(0‿9‿⟨1,0,0,1⟩⊸≡)Extend⁼Extend 0‿9‿⟨1,0,0,1,0⟩
  Next ← {c‿o‿v : ⟨c+1,o+2,rules∊˜<˘5⊸↕v⟩}
  {
    1=part ?
      {g‿o‿v : +´v×o+↕≠v}Next⌾Extend⍟20 ⟨0,0,initial⟩
    ; # the following code doesn't check the moving direction.
      {g‿o‿v : +´v×(o+50000000000-g)+↕≠v}⊑(((Next⌾Extend)⊸⋈)⊣´)•_while_(≢○(2⊸⊑)´)⟨0,0,initial⟩‿⟨0,0,⟨⟩⟩
  }
}
