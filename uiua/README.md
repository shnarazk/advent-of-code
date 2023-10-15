# Try Uiua!

- https://www.uiua.org
- https://github.com/uiua-lang/uiua

## Performance against BQN

#### pre 0.0.20 (a14db387302f97eff7373286df541cc3f60169d0)

```
nix$ cat pi.ua
×4;⍥(|2.2 +1⊙(+÷∶2/×+1_3×4).)/× 50_1000_1000 0 0
nix$ time uiua run --no-format pi.ua
3.1415926445762157
uiua run --no-format pi.ua  23.85s user 0.10s system 96% cpu 24.714 total
```

So the implementation is about 5.34 times slower than CBQN.

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
