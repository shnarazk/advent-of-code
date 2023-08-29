# Implementation memo

```
CBQN on commit 86c570a65310fbb882f677c5123c8deeaf9fc2b1
built with FFI, singeli native aarch64, replxx
```

| y2022  |      LoC | p1 (sec) | p2 (sec) |
|--------|---------:|---------:|---------:|
| day 01 |        1 |    0.185 |    0.166 |
| day 02 |       27 |        0 |        0 |
| day 03 |        5 |        0 |        0 |
| day 04 |        6 |    0.001 |    0.001 |
| day 05 |       18 |    0.001 |    0.001 |
| day 06 |        1 |        0 |        0 |
| day 07 |       27 |    0.027 |    0.027 |
| day 08 |        8 |    0.187 |    0.142 |
| day 09 |       43 |    0.865 |    0.313 |
| day 10 |       11 |    0.008 |    0.008 |
| day 11 |       33 |    0.001 |    0.247 |
| day 12 |       36 |    1.409 |    1.402 |
| day 13 |       47 |    0.536 |    0.576 |
| day 14 |       19 |    0.012 |    0.004 |
| day 15 |       48 |        0 |    0.008 |
| day 16 |       57 |    0.046 |   71.737 |
| day 17 |      113 |     0.99 |   10.336 |
| day 18 |       78 |    0.004 |    1.144 |
| day 19 |       25 |    0.879 |   32.703 |
| day 20 |       25 |    0.617 |    6.134 |
| day 21 |       22 |    0.162 |    4.072 |
| day 22 |       62 |    0.003 |    0.005 |
| day 23 |       29 |    0.104 |     9.57 |
| day 24 |       24 |    0.005 |    0.013 |
| day 25 |       17 |        0 |        0 |

## at day14

My BQN is too slow!

> A particular problem was that in-place mutation ⌾(i⊸⊑) is only fast for very simple cases. Of course, this problem only arises because BQN's arrays are immutable, highlighting that immutable arrays, despite being perfect in every way, can be a pain.

https://github.com/mlochbaum/BQN/blob/master/community/aoc.md

We need to use matrix [less](https://github.com/shnarazk/advent-of-code/issues/30).

| implementation | time | matrix access |
|----------------|------|--------------:|
| [my bqn](https://github.com/shnarazk/advent-of-code/blob/main/bqn/2022/day14.bqn)         | 96.0 |   $O(N^2)$    |
| - on cbqn [05c12703](https://github.com/dzaima/CBQN/tree/05c1270344908e98c9f2d06b3671c3646f8634c3) | 92.45 |
| - on cbqn [4a6877a8](https://github.com/dzaima/CBQN/tree/4a6877a87a81f181942039ac609dcffd17e80dd0)sengeli | 96.45       |
| line-based propagation | 5.66 | $O(N)$  |
| - on cbqn a175c4 | 0.04 | |
| in rust        | 0.17 |   $O(N^2)$    |
| [dzaima/aoc/2022/BQN/14.bqn](https://github.com/dzaima/aoc/blob/master/2022/BQN/14.bqn) |  0.03 | ??? |

!!!

## at day19

| description | performance |
|-------------|-------------|
| committed one, using 'and' |   1098.02s user 5.32s system 99% cpu 18:25.33 total  |
| modified version after the merge, using [multiple tests](https://mlochbaum.github.io/BQN/doc/block.html#predicates) |  847.80s user 4.64s system 99% cpu 14:13.30 total |
| rewrote after 61b51f6 |  793.44s user 6.34s system 99% cpu 13:21.41 total |
|rewrote after 6f95c23 |  787.28s user 5.05s system 99% cpu 13:13.02 total  |
| e687d86 | 545.83s user 0.41s system 99% cpu 9:06.65 total |

- [my memo](https://shnarazk.github.io/2023/2023-03-07-aoc2022-day19/) in Japanese.

-----

## day22

| y⋈x| ·‿0 | ·‿1 | ·‿2 |
|---:|:---:|:---:|:---:|
| 0‿·|     |  A  |B    |
| 1‿·|     |  C  |     |
| 2‿·|  D  |  E  |     |
| 3‿·|  F  |     |     |

![](https://user-images.githubusercontent.com/997855/258643960-ab58710f-5a0a-435c-a04c-16a7e592bde9.png)

| y⋈x | ·‿¯1| ·‿0 | ·‿1 |
|----:|:---:|:---:|:---:|
|¯1‿· |     | F   |     |
| 0‿· | D   | A   | B   |
| 1‿· |     | C   |     |


| y⋈x | ·‿¯1| ·‿0 | ·‿1 |
|----:|:---:|:---:|:---:|
|¯1‿· |     | F   |     |
| 0‿· | A   | B   | E   |
| 1‿· |     | C   |     |

| y⋈x | ·‿¯1| ·‿0 | ·‿1 |
|----:|:---:|:---:|:---:|
|¯1‿· |     | A   |     |
| 0‿· | D   | C   | B   |
| 1‿· |     | E   |     |

| y⋈x | ·‿¯1| ·‿0 | ·‿1 |
|----:|:---:|:---:|:---:|
|¯1‿· |     | C   |     |
| 0‿· | A   | D   | E   |
| 1‿· |     | F   |     |

| y⋈x | ·‿¯1| ·‿0 | ·‿1 |
|----:|:---:|:---:|:---:|
|¯1‿· |     | C   |     |
| 0‿· | D   | E   | C   |
| 1‿· |     | F   |     |

| y⋈x | ·‿¯1| ·‿0 | ·‿1 |
|----:|:---:|:---:|:---:|
|¯1‿· |     | D   |     |
| 0‿· | A   | F   | E   |
| 1‿· |     | B   |     |
