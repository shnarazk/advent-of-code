# Implementation memo

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
| in rust        | 0.17 |   $O(N^2)$    |
| [dzaima/aoc/2022/BQN/14.bqn](https://github.com/dzaima/aoc/blob/master/2022/BQN/14.bqn) |  0.03 | ??? |


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

| y⋈x| ·‿0 | ·‿1 | ·‿0 |
|---:|:---:|:---:|:---:|
| 0‿·|     |  A  |B    |
| 1‿·|     |  C  |     |
| 2‿·|  D  |  E  |     |
| 3‿·|  F  |     |     |


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
| 0‿· | D   | F   | E   |
| 1‿· |     | B   |     |
