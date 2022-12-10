## Solve'em in [BQN](https://github.com/mlochbaum/BQN)!

- https://bqnpad.mechanize.systems/

### Usage

At the top of the working tree of this repository

```
$ bqn/2022/dayDD.bqn data/2022/input-dayDD.txt
```

You may be able to omit the date file.

```
$ bqn/2022/dayDD.bqn
```

For some programs, you need to use `$PWD` to get an absolute path:

```
$ bqn/2022/dayDD.bqn $PWD/data/2022/input-dayDD.txt
```

## editorial configuration

[helix](https://helix-editor.com)

```
[[language]]
name = "bqn"
# scope = "scope.bqn"
# injection-regex = "^bqn"
file-types = ["bqn"]
comment-token = "#"
indent = { tab-width = 2, unit = "  " }
roots = []
[language.auto-pairs]
'⟨' = '⟩'
```
