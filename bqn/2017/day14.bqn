Solve ⇐ {env‿part 𝕊 data :
  util ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
  ⟨knothash⟩← •Import "/2017/knot-hash.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  util.Debug data ⊑ ↩
  {
    1=part ? +´{+´0 KnotHash data∾"-"∾•Repr 𝕩}¨↕128 ;
    @
  }
}
