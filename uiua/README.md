# Try Uiua!

- https://www.uiua.org
- https://github.com/uiua-lang/uiua

## Performance against BQN on M1

#### pre 0.0.21 (3df882b2c3b5a8cdf38f406d71e7a4613a395c68)

- Parallelized Uiua

```
NumThreads ← 1
Step ← ×NumThreads 4
x ← now
⍤ "pi" <0.01⌵-3.1415/+wait≡spawn(|1 ⊙;⍥(|2.2 ⊙'+Step+÷∶8/×,)⌈÷NumThreads/× 50_1000_1000 0) ∵'+1_3×4⇡NumThreads
&p ⊂ NumThreads - x now
```

|NumThreads | wall-clock time (sec)|
|----------:|------:|
|1          | 26.202|
|2          | 18.669|
|3          | 14.022|
|4          | 10.429|
|5          | 13.450|
|6          | 14.841|
|7          | 15.834|

- SIMD BQN

```
n‿chunk ← ⟨50×1000×1000,1000⟩
seed‿span ← ⟨3+4×↕chunk,4×chunk⟩
sum ← 0
Term ← {
  diff ← +´÷×⟜(¯2⊸+)𝕩+seed
  sum diff⊸+↩
  𝕩+span
}
Term⍟(n÷chunk)0
•Show pi ← 8×sum
```

```
nix$ time cbqn misc/ppi.bqn
3.1415926435898
cbqn misc/ppi.bqn  0.13s user 0.01s system 97% cpu 0.138 total
```

So the implementation is about 80.22 times slower than CBQN o3n.

#### pre 0.0.20 (a14db387302f97eff7373286df541cc3f60169d0)

```
nix$ cat misc/pi.ua
×4;⍥(|2.2 +4⊙(+÷∶2/×).)/× 50_1000_1000 1_3 0
# ×4;⍥(|2.2 ⊃'+4(+÷∶2/×))/× 50_1000_1000 1_3 0
nix$ time uiua run --no-format misc/pi.ua
3.1415926445762157
uiua run --no-format misc/pi.ua  17.12s user 0.03s system 95% cpu 17.907 total

nix$ cat misc/pi.bqn
•Show 4×1⊑{⟨4+𝕨,𝕩+2÷×´𝕨⟩}´⍟(×´50‿1000‿1000) ⟨1‿3,0⟩
nix$ time cbqn misc/pi.bqn
3.1415926445762157
cbqn misc/pi.bqn  3.00s user 0.01s system 99% cpu 3.027 total
```

So the implementation is about 5.71 times slower than CBQN.

#### pre 0.0.19 (53578133c1dcc4281f8f26772b1eef5799491c66)

```
nix$ cat pi.ua
×4;⍥(|2.2 +1⊙(+÷∶2/×+1_3×4).)/× 50_1000_1000 0 0
nix$ time uiua run pi.ua
3.141592644576
uiua run pi.ua  28.03s user 0.05s system 96% cpu 29.129 total
```

So the implementation is about 6.28 times slower than CBQN.
Better one is slightly slower.

```
nix$ cat pi.ua
×4;⍥(|2.2 ⊃'+1(+÷∶2/×+1_3×4))/× 50_1000_1000 0 0
nix$ time uiua run pi.ua
3.1415926445762157
uiua run pi.ua  29.80s user 0.03s system 96% cpu 30.771 total
```

#### pre0.0.18

```
nix$ cat pi.ua
×4;⍥(|2.2 +1∶+⊙∶÷∶2/×+1_3×4.)/× 50_1000_1000 0 0
nix$ time uiua run pi.ua
3.141592644576
uiua run pi.ua  35.63s user 0.04s system 97% cpu 36.533 total

nix$ cat pi.bqn
•Show 4×1⊑{⟨1+𝕨,𝕩+2÷×´3‿1+4×𝕨⟩}´⍟(×´50‿1000‿1000) 0‿0
nix$ time cbqn pi.bqn
3.1415926445762157
cbqn pi.bqn  4.46s user 0.01s system 99% cpu 4.484 total
```

So the implementation is about 8 times slower than CBQN.

Slow and premature but with Rust-y environment + nix-y execution/development environment. That's nice!

## Helix configuration

- https://github.com/helix-editor/helix/wiki/How-to-install-the-default-language-servers#uiua
- https://github.com/shnarazk/tree-sitter-uiua
