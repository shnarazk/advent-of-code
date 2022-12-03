## Solve'em in [BQN](https://github.com/mlochbaum/BQN)!

### Usage

Due to the incovenient handling of relative path, we need to use `$PWD` for getting a data file like:

```
# at the top of the working tree of this repository
$ cbqn bqn/2022/dayDD.bqn $PWD/data/2022/input-dayDD.txt
```