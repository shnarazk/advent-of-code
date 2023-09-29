# Try UIUA!

- https://www.uiua.org
- https://github.com/uiua-lang/uiua

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
indent = { tab-width = 4, unit = "    " }
```
