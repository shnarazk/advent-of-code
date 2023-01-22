## Solve'em in [BQN](https://github.com/mlochbaum/BQN)!

- https://bqnpad.mechanize.systems/
- https://github.com/shnarazk/learn-bqn

### Usage

#### new driver, 2023-01-22
 
Run the following here:

```
$ ./aoc DD PP
```
- `DD ∊ 1+↕25` for day of 2022
- `PP ∊ 1+↕2` for part 

For example run for both part 2 of day 15, 2022:

```
$ ./aoc.bqn 15 2
```

#### for old programs

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
