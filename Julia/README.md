Top level is `Aoc_Julia` package.
Tests are provided by `AoC` submodule.

## Building and using a Julia sysimage

A reusable sysimage build script is provided at `scripts/build_sysimage.jl`. This speeds up startup and reduces compilation latency for repeated runs.

- Build a sysimage inferred from the current project:
  - `julia scripts/build_sysimage.jl --project=. --name=AoC_JuliaSys`
- Overwrite an existing sysimage:
  - `julia scripts/build_sysimage.jl --project=. --name=AoC_JuliaSys --force`
- Use a warmup script to record precompile statements:
  - `julia scripts/build_sysimage.jl --project=. --warmup=scripts/warmup.jl`
- Specify packages explicitly (instead of inferring from the project):
  - `julia scripts/build_sysimage.jl --packages=AoC,ParserCombinator`
- Target a specific CPU (optional):
  - `julia scripts/build_sysimage.jl --project=. --cpu-target=native`

By default, the output is written to `build/sysimages/<NAME>.{dylib|so|dll}` depending on your OS. For example, with `--name=AoC_JuliaSys` on macOS:
- `build/sysimages/AoC_JuliaSys.dylib`

Run Julia using the sysimage:
- `julia --sysimage=build/sysimages/AoC_JuliaSys.dylib your_script.jl`

Notes:
- A sysimage is not a standalone executable; you still launch `julia` with `--sysimage=...`.
- The `scripts/warmup.jl` file contains a minimal warmup routine you can extend to cover common hot paths in your workflow.
