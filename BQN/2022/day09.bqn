DirVec ← {
  F⟨"U",r⟩ : ⟨ 0,-1⟩ ;
  F⟨"D",r⟩ : ⟨ 0, 1⟩ ;
  F⟨"L",r⟩ : ⟨-1, 0⟩ ;
  F⟨"R",r⟩ : ⟨ 1, 0⟩ ;
  "error" ! 1
}
UpdateTail ← {
  ⟨dx,dy⟩ ← 𝕨 -𝕩
  𝕩 +¨ {
    1<|dx×dy ? ⟨dx÷|dx,dy÷|dy⟩ ;
    1<|dx    ? ⟨dx÷|dx,     0⟩ ;
    1<|dy    ? ⟨0     ,dy÷|dy⟩ ;
               ⟨0     ,0⟩
  }
}
Update ← {
  ⟨dir,0⟩ F state : state ;
  ⟨dir,n⟩ F ⟨head,tail,history⟩ :
    h ← head+DirVec 𝕨
    t ← h UpdateTail tail
    ⟨dx,dy⟩ ← h -tail
    ⟨dir,n-1⟩ F ⟨h,t,{⟨t⟩⊑∘∊history ? history ; ⟨t⟩∾history}⟩
}
Update2 ← {
  ⟨dir,0⟩ F state : state ;
  ⟨dir,n⟩ F ⟨knots,history⟩ :
    Propagate ← {
      last F ⟨⟩ : ⟨⟩ ;
      ⟨head⟩‿tail ← 1(↑⋈↓)𝕩
      h ← 𝕨 UpdateTail head
      ⟨h⟩∾h Propagate tail
    }
    ⟨head,tail⟩ ← (⊑⋈1⊸↓)knots
    h ← head+DirVec 𝕨
    t ← h Propagate tail
    ⟨dir,n-1⟩F⟨⟨h⟩∾t,{⟨𝕩⟩⊑∘∊history ? history ; ⟨𝕩⟩∾history}⊑⌽t⟩
}

Solve ⇐ {env‿part 𝕊 data :
  lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  moves ← (1⊸↑⋈(lib.ParseInt 2⊸↓))¨data
  {1=part ? ≠2⊑⟨⟨0,0⟩,⟨0,0⟩,⟨⟩⟩Update´⌽moves ; ≠1⊑⟨⟨0,0⟩¨↕10,⟨⟩⟩Update2´⌽moves}
}
