# Lean4

![Lean4-image](https://github.com/user-attachments/assets/5cdc3698-2704-4794-b9ab-0c4f2883a3a3)

_generated by DALL-E_

- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/title.html#functional-programming-in-lean)
- [library doc](https://leanprover-community.github.io/mathlib4_docs) of [lean4](https://github.com/leanprover/lean4) / [batteries](https://github.com/leanprover-community/batteries) moved from 'std4' /
[mathlib4](https://github.com/leanprover-community/mathlib4)

### Benchmarks

```
$ lake exe aoc -y YEAR -b
```

#### y2024

|day|time(ms) 4.14.0|4.15.0| 4.19.0 |  Rust1.84|
|----:|--------:|--------:|--------:|---------:|
|  01 |     1.3 |     1.0 |     1.2 |      1.6 |
|  02 |     2.9 |     2.3 |     2.5 |      1.5 |
|  03 |     2.2 |     2.2 |     2.4 |      0.8 |
|  04 |     9.9 |     9.3 |    10.6 |      4.0 |
|  05 |    25.6 |    24.7 |    25.9 |      8.3 |
|  06 |   628.9 |   635.8 |   725.1 |     30.8 |
|  07 |   654.5 |   656.5 |   964.8 |     48.6 |
|  08 |         |     0.7 |     0.6 |      0.4 |
|  09 |         |   357.1 |   369.6 |     10.5 |
|  10 |         |    12.7 |    12.4 |      1.1 |
|  11 |         |         |         |      4.8 |
|  12 |         |         |         |      5.5 |
|  13 |         |         |         |      0.6 |
|  14 |         |         |         |    480.9 |
|  15 |         |         |         |      1.5 |
|  16 |         |         |         |    161.3 |
|  17 |         |         |         |      1.2 |
|  18 |         |         |         |      2.0 |
|  19 |         |         |         |      3.4 |
|  20 |         |         |         |     34.7 |
|  21 |         |         |         |      1.1 |
|  22 |         |         |         |    383.8 |
|  23 |         |         |         |     53.4 |
|  24 |         |         |         |      0.2 |
|  25 |         |         |         |      1.5 |

Note: `*` for algorithmic breaking changes

#### y2023

|day|time(msec) by 4.7?|4.10.0-rc1| 4.12.0 |4.13.0-rc3|4.14.0-rc2|
|----:|----------:|------------:|---------:|---------:|---------:|
|  01 |       3.4 |        2.9  |      4.5 |      3.5 |      4.1 |
|  02 |       1.4 |        1.0  |      1.4 |      1.6 |      1.5 |
|  03 |       5.8 |        7.1  |      8.6 |      8.3 |      7.8 |
|  04 |      17.7 |        1.7  |      2.7 |      2.6 |      2.1 |
|  05 |       1.7 |        1.6  |      1.8 |      1.8 |      1.9 |
|  06 |       0.1 |        0.0  |      0.0 |      0.3 |      0.4 |
|  07 |       5.3 |        2.1  |      2.4 |      2.2 |      2.3 |
|  08 |      59.5 |       61.4  |     62.7 |     57.0 |     60.7 |
|  09 |       5.0 |        2.2  |      1.9 |      3.6 |      2.9 |
|  10 |     705.0 |      825.3  |  * 782.3 |  * 812.2 |    876.0 |
|  11 |       9.6 |        6.6  |      6.7 |      6.9 |      3.4 |
|  12 |     182.3 |      187.0  |    185.1 |    189.0 |    187.1 |
|  13 |           |             |          |     50.7 |     55.9 |
|  14 |           |             |          |    104.7 |    115.9 |
|  15 |           |             |          |      3.8 |      4.1 |
|  16 |           |             |          |    898.7 |    932.6 |
|  17 |           |             |          |   1159.1 |   1203.2 |
|  18 |           |             |          |     97.9 |     97.9 |
|  19 |           |             |          |      1.7 |      2.6 |
|  20 |           |             |          |    118.9 |    120.9 |

Note: `*` for algorithmic breaking changes
