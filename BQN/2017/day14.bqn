Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashset⟩ ← •Import¨"/util.bqn"‿"/hashset.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  ⟨knothash⟩← •Import "/2017/knot-hash.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  data ⊑ ↩
  {
    1=part ? +´{+´0 KnotHash data∾"-"∾•Repr 𝕩}¨↕128 ;
    map ← ∾{0 KnotHash data∾"-"∾•Repr 𝕩}¨↕128
    unused ← Hashset map/⥊↕128‿128
    Linked ← {1=+´|𝕨-𝕩}
    Group ← {𝕊 unused :
      g ← Hashset⊏k ← unused.Values⁼@
      {g.Set¨𝕩 ⍷∘∾∘({(𝕩⊸Linked∧¬∘g.Has)¨⊸/k}¨) ↩ ⋄ 𝕩}•_while_(⟨⟩⊸≢)⊏k
      g
    }
    {unused.Delete¨(Group unused).Values⁼@ ⋄ 1+𝕩}•_while_{𝕤 ⋄ 0<unused.Count@}0
  }
}
