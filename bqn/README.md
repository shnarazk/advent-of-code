## Solve'em in [BQN](https://github.com/mlochbaum/BQN)!

- https://bqnpad.mechanize.systems/
- https://github.com/shnarazk/learn-bqn

### Usage

#### A new driver, 2023-01-22
 
Run [the driver](https://github.com/shnarazk/advent-of-code/blob/main/aoc.bqn) at the top level of the working tree (not here):

```
$ ./aoc.bqn YYYY DD PP [ALT]
```
- `YYYY` for year
- `DD ∊ 1+↕25` for day of 2022
- `PP ∊ 1+↕2` for part 

For example run for the part 2 of day 15, 2022:

```
$ ./aoc.bqn 2022 15 2
```

#### For old programs

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

## About editorial configuration

- [my settings](https://github.com/shnarazk/learn-bqn/blob/main/helix.md) on [helix](https://helix-editor.com)
