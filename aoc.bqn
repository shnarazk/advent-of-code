#!/usr/bin/env cbqn
lib ← •Import "bqn/lib.bqn"
day‿part‿prog‿data ← {
  𝕊 ⟨day⟩:
    ⟨
      •BQN day,
      3,
      lib.AbsolutePath "bqn/2022/day"∾day∾".bqn",
      lib.AbsolutePath "data/2022/input-day"∾day∾".txt"
    ⟩;
  𝕊 ⟨day,part⟩:
    ⟨
      •BQN day,
      •BQN part,
      lib.AbsolutePath "bqn/2022/day"∾day∾".bqn",
      lib.AbsolutePath "data/2022/input-day"∾day∾".txt"
    ⟩;
  𝕊 ⟨day,part,suf⟩:
    ⟨
      •BQN day,
      •BQN part,
      lib.AbsolutePath "bqn/2022/day"∾day∾".bqn",
      lib.AbsolutePath "data/2022/input-day"∾day∾"-"∾suf∾".txt",
    ⟩;
  "aoc driver takes day part [alt]" ! 0
} •args
(•Fmt day) lib.Debug data
bqn ← •Import prog
{ 2|part  ? 1 bqn.Run •FLines data; @ }
{ 2|»part ? 2 bqn.Run •FLines data; @ }
