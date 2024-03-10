Solve ⇐ {env‿part 𝕊 data :
  util‿⟨hashmap⟩ ← •Import¨"/util.bqn"‿"/hashmap.bqn"∾˜¨<"." env.Var⌾⋈ "BQN_LIB"
  data (-⟜'A'∘⊑¨·1‿7⊸⊏" "⊸util.Split)¨ ↩
  p ← Hashmap˜⟨⟩ # map from node to parents
  {𝕨 p.Set∧⟨𝕩⟩∾⟨⟩ p.Get 𝕨}˜´¨data
  children ← ⍷p.Values⁼@
  roots ← (¬∊⟜children)⊸/↕26
  p.Set⟜⟨⟩¨roots
  {
    1=part ?
      'A'+1⊑{cands‿seq :
        next ← ⊑∧(∧´·(∊⟜seq)p.Get)¨⊸/cands
        ⟨next⊸≠¨⊸/cands,seq∾next⟩
      }•_while_(⟨⟩≢⊑)(↕26)‿⟨⟩
      ;
    r ← {seconds‿remain‿shift :
      # purge finished tasks then check if there are executable tasks now
      unfinished ← remain∾⍷1⊸⊑¨ shift (0≠⊑)◶⟨0‿∞,⊢⟩¨ ↩
      executables ← (¬·∨´·(∊⟜unfinished)p.Get)¨⊸/remain
      {
        ⟨⟩≢executables ?
        task ← ⊑∧executables
        workerIndex ← ((0=⊑)∨(∞=1⊸⊑))¨shift
        ∨´workerIndex ?
          workerIndex {𝕩⊸⊐⌾⋈1} ↩
          ⟨seconds,task⊸≠¨⊸/remain,⟨61+task,task⟩⌾(workerIndex⊸⊑)shift⟩
        ;
        # otherwise go forward to the time a task is finished
        elapse ← ⊑⊑∧(∞≠1⊸⊑)¨⊸/shift
        ⟨seconds+elapse,remain,{⟨0⌈𝕨-elapse,𝕩⟩}´¨shift⟩
      }
    }•_while_(⟨⟩≢1⊸⊑)⟨0,↕26,0‿∞¨↕5⟩
    (⊑r)+⌈´⊑¨2⊑r
  }
}
