#!/usr/bin/env cbqn
env←{v⇐⍉>⊑∘⊐⟜'='⊸(↑⋈1⊸↓∘↓)¨{-¬(¬×1++`)𝕩=@+10}⊸⊔1⊑•SH<"env"⋄Var⇐{⊐⟜𝕩⊸⊏⟜(∾⟜𝕨)˝v}}
lib ← •Import "/util.bqn"∾˜"." env.Var⌾⋈ "BQN_LIB"
aoc ← ".." env.Var⌾⋈ "AOC_REPO_DIR"
Fill ← {template 𝕊 value : value∾˜(template-○≠value)↑template}
year‿day‿part‿prog‿datafile ← {
  ⟨year,day⟩ :
    y‿d ← ⟨"2020","00"⟩Fill¨year‿day
    ⟨y,d,3,                aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn",aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"⟩ ;
  ⟨year,day,part⟩ :
    y‿d ← ⟨"2020","00"⟩Fill¨year‿day
    ⟨y,d,⌊•Parsefloat part,aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn",aoc∾"/data/"∾y∾"/input-day"∾d∾".txt"⟩ ;
  ⟨year,day,part,suf⟩ :
    y‿d ← ⟨"2020"∾"00"⟩Fill¨year‿day
    ⟨y,d,⌊•Parsefloat part,aoc∾"/bqn/"∾y∾"/day"∾d∾".bqn",aoc∾"/data/"∾y∾"/input-day"∾d∾"-"∾suf∾".txt"⟩ ;
  lib.color.red lib.term.Outln "AoC driver takes YEAR DAY PART [ALT]"
  •Exit 1
}{•name<⊸(⊑∘∊)"2016"‿"2021"‿"2022"‿"2023" ? •name <⊸∾•args ; •args}
•Out"Year "∾year∾" Day "∾day∾" on: "∾datafile
bqn ← •Import prog
{0=part    ? •Out"DEBUG: "∾•Fmt env‿0 bqn.Solve•FLines datafile ; @}
{2|part    ? •Out"Part1: "∾•Fmt env‿1 bqn.Solve•FLines datafile ; @}
{2|⌊part÷2 ? •Out"Part2: "∾•Fmt env‿2 bqn.Solve•FLines datafile ; @}
