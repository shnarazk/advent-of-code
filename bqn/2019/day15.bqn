Solve ⇐ {env‿part 𝕊 data :
  util‿geo‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/geometry.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data util.ParseInts∘⊑ ↩
  intcode ← •Import "/2019/intcode.bqn"∾˜"." env.Var⌾⋈ "AOC_BQN_DIR"
  droid ← intcode.Intcode data
  Turn ← {
    𝕊  𝕩 : ⟨¯1‿0,0‿1,1‿0,0‿¯1⟩{𝕨⊑˜4| 1+𝕨⊸⊐⌾⋈𝕩}𝕩 ;
    𝕊⁼ 𝕩 : ⟨¯1‿0,0‿1,1‿0,0‿¯1⟩{𝕨⊑˜4|¯1+𝕨⊸⊐⌾⋈𝕩}𝕩
  }
  EncodeDir ← ⟨0‿0,¯1‿0,1‿0,0‿1,0‿¯1⟩⊸⊐⌾⋈
  Check ← {((droid.Input⋈EncodeDir 𝕩).Run@).Output@}
  map ← 0‿0 Hashmap○⋈ 1
  target ← ∞‿∞
    pos ← 0‿0
    dir ← 0‿¯1
    {
      {
        0 : (dir+pos)map.Set ∞ ⋄ "# hit wall" util.Debug dir Turn ↩ ;
        1 : "# move" util.Debug pos dir⊸+ ↩ ⋄ pos map.Set 1 ⋄ dir Turn⁼ ↩ ;
        2 : "# found" util.Debug pos dir⊸+ ↩ ⋄ pos map.Set 1 ⋄ target ↩ pos
      }¨Check dir
      1+𝕩
    }•_while_{𝕤 ⋄ ∞‿∞≡target}0
    min‿max ← (⌊´⋈⌈´)map.Values⁼@
    m ← ∞¨↕shape ← max¬min
    mask ← m{p‿d 𝕊 𝕩 : d⌾((p-min)⊸⊑)𝕩}´map.Values⁼˜@
  {
    1=part ? (target-min)⊑⊑{x‿pre : ⟨mask×x⌊1+⌊´¨∞ geo.Neighbor5 x,x⟩}•_while_(≢´)⟨0⌾((0‿0-min)⊸⊑)m,@⟩ ;
    ⊑{step‿x : ⟨1+step,mask×x⌊⌊´¨∞ geo.Neighbor5 x⟩}•_while_(∨´·2⊸=·⥊1⊸⊑)⟨0,1⌾((target-min)⊸⊑)1+mask⟩
  }
}
