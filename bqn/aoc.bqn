#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1↓↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
util‿aoc ← (•Import∾⟜"/util.bqn")⊸⋈´ "."‿".." env.Var "BQN_LIB"‿"AOC_REPO_DIR"
year‿day‿part‿prog‿datafile ← {
  ⟨year,day⟩          :
    y‿d ← ⟨"2020","00"⟩util.LeftFill¨year‿day
    ⟨y,d,3,                aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn",aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"⟩ ;
  ⟨year,day,part⟩     :
    y‿d ← ⟨"2020","00"⟩util.LeftFill¨year‿day
    ⟨y,d,⌊•Parsefloat part,aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn",aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"⟩ ;
  ⟨year,day,part,alt⟩ :
    y‿d ← ⟨"2020","00"⟩util.LeftFill¨year‿day
    ⟨y,d,⌊•Parsefloat part,aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn",aoc∾"/data/"∾y∾"/input-day"∾d∾"-"∾alt∾".txt"⟩ ;
  util.color.red util.term.Outln "AoC driver takes YEAR DAY PART [ALT]"
  •Exit 1
}{util.ValidYear •name ? •name<⊸∾•args ; •args}
•Out "Year "∾year∾" Day "∾day∾" on: "∾datafile
bqn ← •Import⊑util.ExistsOrExit¨prog‿datafile
{0=part    ? •Out "DEBUG: "∾•Fmt env‿0 bqn.Solve•FLines datafile ; @}
{2|part    ? •Out "Part1: "∾•Fmt env‿1 bqn.Solve•FLines datafile ; @}
{2|⌊part÷2 ? •Out "Part2: "∾•Fmt env‿2 bqn.Solve•FLines datafile ; @}
