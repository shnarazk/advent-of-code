## y2022

- rustc-1.91
- Apple Silicon M3

|   day | time(ms)|
|------:|--------:|
| day1  |     0.6 |
| day2  |     0.3 |
| day3  |     0.3 |
| day4  |     0.3 |
| day5  |     0.4 |
| day6  |     0.5 |
| day7  |     0.4 |
| day8  |     9.3 |
| day9  |     1.1 |
| day10 |     0.2 |
| day11 |    12.5 |
| day12 |     1.9 |
| day13 |     1.4 |
| day14 |     4.7 |
| day15 |     0.2 |
| day16 |   601.7 |
| day17 |  6452.7 |
| day18 |     2.5 |
| day19 |   997.1 |
| day20 |   314.5 |
| day21 |     5.0 |
| day22 |     2.5 |
| day23 |   416.8 |
| day24 |   642.2 |
| day25 |     0.3 |
| y2022 |  9469.4 |

### day14 https://adventofcode.com/2022/day/14
buckets floading problem similar with [y2018 day17](https://adventofcode.com/2018/day/17)

BQN version uses much better idea.

### day15 https://adventofcode.com/2022/day/15
overlapping diamonds problem

#### 'the intersection' of $(p_x,p_y)$ and $(q_x,q_y)$
![geogebra-export-3](https://user-images.githubusercontent.com/997855/210023849-64c6c25b-8d7d-47c7-8f7d-72db4ea0e152.svg)

- $(x - p_x) + p_y = -(x - q_x) + q_y \longrightarrow x = (p_x + q_x - p_y + q_y)/2, y = (-p_x + 2q_x + p_y + 2q_y)/2$ 
- $-(x - p_x) + p_y = (x - q_x) + q_y \longrightarrow x = (p_x + q_x + p_y - q_y)/2, y = (-3p_x - q_x -3p_y + q_y)/2$

### day16 https://adventofcode.com/2022/day/16
the first path finding problem of this year

### day17 https://adventofcode.com/2022/day/17
find a repetition pattern in a long sequence

### day21 https://adventofcode.com/2022/day/21
graph reduction

### day22 https://adventofcode.com/2022/day/22
path tracing on a surface in 3D space

### day23 https://adventofcode.com/2022/day/23
2D cellar automaton

![スクリーンショット 2022-12-24 1 19 02](https://user-images.githubusercontent.com/997855/209366726-03437e6c-7eef-44dc-947f-7670eecd6129.png)

### day24 https://adventofcode.com/2022/day/24
shape-changing path finding problem








