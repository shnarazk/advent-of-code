# Try Uiua!

- https://www.uiua.org
- https://github.com/uiua-lang/uiua

### pre 0.0.19 (53578133c1dcc4281f8f26772b1eef5799491c66)

```
nix$ cat pi.ua
×4;⍥(|2.2 +1⊙(+÷∶2/×+1_3×4).)/× 50_1000_1000 0 0
nix$ time uiua run pi.ua
3.141592644576
uiua run pi.ua  28.03s user 0.05s system 96% cpu 29.129 total
```

So the implementation is about 6.28 times slower than CBQN.

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

Sure, I'll copy it to the wiki.

```toml
[language-server.uiua-lsp]
command = "uiua"
args = ["lsp"]

[[language]]
name = "uiua"
scope = "source.uiua"
injection-regex = "uiua"
file-types = ["ua"]
roots = []
auto-format = true
comment-token = "#"
language-servers = [ "uiua-lsp" ]
indent = { tab-width = 2, unit = "  " }
```
