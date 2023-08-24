#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1⊸↓∘↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
util‿aoc ← (•Import∾⟜"/util.bqn")⊸⋈´ "."‿".." env.Var "BQN_LIB"‿"AOC_REPO_DIR"
⟨year⟩‿blacklist ← util.ParseInt¨⌾(1⊸⊑)1(↑⋈↓)•args
y ← "2020" util.LeftFill year
result ← {
  d ← "00" util.LeftFill •Fmt 𝕩
  ∊⟜blacklist⌾⋈ 𝕩 ? d‿"skipped"‿"skipped" ;
  d ← "00" util.LeftFill •Fmt 𝕩
  progfile ← aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn"
  datafile ← aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"
  ∧´•file.Exists¨progfile‿datafile ?
  bqn ← •Import progfile
  util.Progress "day "∾d
  part1 ← (env‿1⊸bqn.Solve)•_timed •FLines datafile
  part2 ← (env‿2⊸bqn.Solve)•_timed •FLines datafile
  d<⊸∾("       "⊸util.LeftFill∘•Fmt)¨(⌊0.5⊸+)⌾(1000⊸×)¨part1‿part2 ;
  d ← "00" util.LeftFill •Fmt 𝕩
  d‿"skipped"‿"skipped"
}¨1+↕25
•Out "| y"∾y∾"  |  part 1 |  part 2 |"
•Out "|--------|--------:|--------:|"
{day‿part1‿part2 : •Out "| day "∾day∾" | "∾part1∾" | "∾part2∾" |"}¨result