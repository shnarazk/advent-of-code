# Try Uiua!

- https://www.uiua.org
- https://github.com/uiua-lang/uiua

```
nix$ cat pi.ua
×4;⍥(|2.2 +1∶+⊙∶÷∶2×+2.+1×4.)/× 50_1000_1000 0 0
nix$ time uiua run pi.ua
3.141592644576
uiua run pi.ua  39.31s user 0.02s system 99% cpu 39.438 total

nix$ cat pi.bqn
•Show 4×1⊑{⟨1+𝕨,𝕩+2÷×´3‿1+4×𝕨⟩}´⍟(×´50‿1000‿1000) 0‿0
nix$ time cbqn pi.bqn
3.1415926445762157
cbqn pi.bqn  4.46s user 0.01s system 99% cpu 4.484 total
```

So the implementation is about 10 times slower than CBQN.

Slow and too young but with Rust-y environment + nix-y execution/development environment. That's nice!

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
