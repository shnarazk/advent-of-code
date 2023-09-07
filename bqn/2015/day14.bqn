Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  data ↩ (util.ParseInt¨∘(3‿6‿13⊸⊏))¨" ,."⊸util.Tokenize¨data
  Reaches ← {
    seconds 𝕊 speed‿duration‿respite :
    phases ← seconds⌊∘÷duration+respite
    ongoing ← duration⌊seconds-phases×duration+respite
    speed×ongoing+phases×duration
  }
  {
    1=part ? ⌈´2503 Reaches¨data ;
   ⌈´((≠data)↑0){time 𝕊 record : (1⊸+)⌾((⊑⍒time Reaches¨data)⊸⊑)record}´1+↕2503
  }
}
