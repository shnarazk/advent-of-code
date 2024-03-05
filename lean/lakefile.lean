import Lake
open Lake DSL

package «AoC» where
  -- add package configuration options here

lean_lib «AoC» where
  -- add library configuration options here

@[default_target]
lean_exe «aoc» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"
require std from git "https://github.com/leanprover/std4" @ "main"
