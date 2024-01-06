## y2022

|   day |    time |
|------:|--------:|
| day1  |     1.5 |
| day2  |     0.9 |
| day3  |     1.2 |
| day4  |     2.0 |
| day5  |     1.6 |
| day6  |     1.0 |
| day7  |     2.9 |
| day8  |    14.5 |
| day9  |     2.4 |
| day10 |     0.5 |
| day11 |    11.6 |
| day12 |     4.0 |
| day13 |     1.3 |
| day14 |    67.5 |
| day15 |     0.9 |
| day16 | 18747.2 |
| day17 | 21459.9 |
| day18 |     7.0 |
| day19 |  1295.3 |
| day20 |   619.5 |
| day21 |     9.4 |
| day22 |     5.2 |
| day23 |   566.1 |
| day24 |   673.4 |
| day25 |     0.5 |
| y2022 | 43497.3 |

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








