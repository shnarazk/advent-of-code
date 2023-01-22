#!/usr/bin/env cbqn
lib ← •Import "bqn/lib.bqn"

Fill ← { template 𝕊 value: value∾˜(template -○≠ value)↑template }

year‿day‿part‿prog‿datafile ← {
  𝕊 ⟨year,day⟩:
    y ← "2020" Fill year,
    d ← "00" Fill day,
    ⟨
      y,
      d,
      3,
      lib.AbsolutePath "bqn/"∾y∾"/day"∾d∾".bqn",
      lib.AbsolutePath "data/"∾y∾"/input-day"∾d∾".txt"
    ⟩;
  𝕊 ⟨year,day,part⟩:
    y ← "2020" Fill year,
    d ← "00" Fill day,
    ⟨
      y,
      d,
      •BQN part,
      lib.AbsolutePath "bqn/"∾y∾"/day"∾d∾".bqn",
      lib.AbsolutePath "data/"∾y∾"/input-day"∾d∾".txt"
    ⟩;
  𝕊 ⟨year,day,part,suf⟩:
    y ← "2020" Fill year,
    d ← "00" Fill day,
    ⟨
      y,
      d,
      •BQN part,
      lib.AbsolutePath "bqn/"∾y∾"/day"∾d∾".bqn",
      lib.AbsolutePath "data/"∾y∾"/input-day"∾d∾"-"∾suf∾".txt",
    ⟩
  ;
    lib.color.red lib.term.Outln "This aoc driver takes YEAR DAY PART [ALT]"
    •Exit 1
} •args
•Out "Year "∾year∾" Day "∾day∾" on: "∾datafile
bqn ← •Import prog
{ 2|part     ? •Out "Part1: "∾•Fmt 1 bqn.Run •FLines datafile; @ }
{ 2|⌊2÷˜part ? •Out "Part2: "∾•Fmt 2 bqn.Run •FLines datafile; @ }
