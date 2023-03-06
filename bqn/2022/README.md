# Today I learned

## at day07

> The Cells modifier `˘` applies a function to major cells of its argument, much like Each applies to elements. Each result from 𝔽 becomes a major cell of the result, which means they must all have the same shape.

https://github.com/shnarazk/advent-of-code/blob/faf1a1b0d48ffd02981457211851360389f7d9b9/bqn/2022/day07.bqn#L22
https://github.com/shnarazk/advent-of-code/blob/faf1a1b0d48ffd02981457211851360389f7d9b9/bqn/2022/day07.bqn#L26
https://github.com/shnarazk/advent-of-code/blob/faf1a1b0d48ffd02981457211851360389f7d9b9/bqn/2022/day07.bqn#L29


In `F˘m2`, `F` must return values with the identical shape. So I need something like:

```apl
{
   a_case ? do something with side-effect ⋄ ⟨⟩;
   another ? another task w/ side-effect  ⋄ ⟨⟩;
             and something more           ⋄ ⟨⟩
}˘m2
``` 

## at day14

BQN is too slow!

> A particular problem was that in-place mutation ⌾(i⊸⊑) is only fast for very simple cases. Of course, this problem only arises because BQN's arrays are immutable, highlighting that immutable arrays, despite being perfect in every way, can be a pain.

https://github.com/mlochbaum/BQN/blob/master/community/aoc.md

We need to use matrix [less](https://github.com/shnarazk/advent-of-code/issues/30).

| implementation | time | matrix access |
|----------------|------|--------------:|
| [my bqn](https://github.com/shnarazk/advent-of-code/blob/main/bqn/2022/day14.bqn)         | 96.0 |   $O(N^2)$    |
| - on cbqn [05c12703](https://github.com/dzaima/CBQN/tree/05c1270344908e98c9f2d06b3671c3646f8634c3) | 92.45 |
| in rust        | 0.17 |   $O(N^2)$    |
| [github.com/dzaima/aoc/2022/BQN/14.bqn](https://github.com/dzaima/aoc/blob/master/2022/BQN/14.bqn) |  0.03 | ??? |

!!

## at day15

https://mlochbaum.github.io/BQN/doc/logic.html#examples
> (both sides are always evaluated: there's nothing like the shortcutting of && in some languages)

We can't convert [this]( https://github.com/shnarazk/advent-of-code/blob/b9326b2ef1b55ff800461604a9e1c835b64b3f16/bqn/2022/day15.bqn#L42-L44 )

```apl
Sat ← { 
  c 𝕊 0: {(0≤0⊑c)∧(0⊑c≤p2)∧(0≤1⊑c)∧(1⊑c≤p2) ? { ∧´{2⊑𝕩<c Mdist ⟨0⊑𝕩,1⊑𝕩⟩}¨ sensors ? (1⊑c)+(0⊑c)×p2; 0}; 0};
  c 𝕊 n: n
}
```
to

```apl
Sat ← { 
  c 𝕊 0: (0≤0⊑c)∧(0⊑c≤p2)∧(0≤1⊑c)∧(1⊑c≤p2) ∧ { ∧´{2⊑𝕩<c Mdist ⟨0⊑𝕩,1⊑𝕩⟩}¨ sensors ? (1⊑c)+(0⊑c)×p2; 0;
  c 𝕊 n: n
}
```

In BQN, `∧` isn't a short-circuit operator:

```apl
{•Show "didn't expect" ⋄ 1} ∧ 0
```

[online REPL](https://bqnpad.mechanize.systems/s?bqn=eyJkb2MiOiJ74oCiU2hvdyBcImRpZG4ndCBleHBlY3RcIuKLhDF9IOKIpyAwIiwicHJldlNlc3Npb25zIjpbXSwiY3VycmVudFNlc3Npb24iOnsiY2VsbHMiOltdLCJjcmVhdGVkQXQiOjE2NzIxOTY2NjI3MTh9LCJjdXJyZW50Q2VsbCI6eyJmcm9tIjowLCJ0byI6MjksInJlc3VsdCI6bnVsbH19)

But due to the BQN's [header system](https://mlochbaum.github.io/BQN/doc/block.html#predicates), there's a way to make it simple:

```apl
    {{•Show "did expect"⋄0} ? {•Show "didn't expect"⋄1} ? 1 ; 0}
did expect
0
```

So I rewrited like

```apl
Sat ← { 
  c 𝕊 0: {(0≤0⊑c)∧(0⊑c≤p2)∧(0≤1⊑c)∧(1⊑c≤p2) ? { ∧´{2⊑𝕩<c Mdist ⟨0⊑𝕩,1⊑𝕩⟩}¨ sensors ? (1⊑c)+(0⊑c)×p2; 0};
  c 𝕊 n: n
}
```

## at day19

| description | performance |
|-------------|-------------|
| committed one, using 'and' |   1098.02s user 5.32s system 99% cpu 18:25.33 total  |
| modified version after the merge, using [multiple tests](https://mlochbaum.github.io/BQN/doc/block.html#predicates) |  847.80s user 4.64s system 99% cpu 14:13.30 total |
| rewrote after 61b51f6 |  793.44s user 6.34s system 99% cpu 13:21.41 total |
|rewrote after 6f95c23 |  787.28s user 5.05s system 99% cpu 13:13.02 total  | 
| e687d86 | 545.83s user 0.41s system 99% cpu 9:06.65 total |


## at day20

https://mlochbaum.github.io/BQN/doc/repeat.html#array-of-repetition-counts
> Regardless of how numbers in 𝕨𝔾𝕩 are arranged, 𝔽 is evaluated the minimum number of times required to find the result, and regular (positive) applications are all performed before reverse (negative) ones.

Repeat `⍟` seems to need a function that uses the argument ~~with some side effect~~ [like](https://github.com/shnarazk/advent-of-code/blob/f26b28a2ba5afb6f82882f0d2942397d6af976f9/bqn/2022/day20.bqn#L26)

```apl
{Shift¨ ↕n⋄ 1+𝕩}⍟10 0
```

Because the folllowing does not work:

```apl
{•Show "run" ⋄ 1}⍟10 0
```
but the following does:

```apl
{•Show "run" ⋄ 𝕩}⍟10 0
```

So I revised the line like:

```diff
diff --git a/bqn/2022/day20.bqn b/bqn/2022/day20.bqn
index 3330959..2b07000 100755
--- a/bqn/2022/day20.bqn
+++ b/bqn/2022/day20.bqn
@@ -23,5 +23,5 @@ Shift¨ ↕n
 data ↩ 811589153×¨ data
 ⟨next, prev⟩ ↩ ((1⊸+)(⋈○(n⊸|n⊸+))(¯1⊸+)) ↕n
-{Shift¨ ↕n⋄ 1+𝕩}⍟10 0
+n {Shift¨ ↕𝕨}⍟10 0
 •Show +´Trace¨ 1000‿2000‿3000
```

[online REPL](https://bqnpad.mechanize.systems/s?bqn=eyJkb2MiOiLin6h74oCiU2hvdyBcImluY3JlbWVudFwiIOKLhCAxK%2FCdlal94o2fNCAwLCB74oCiU2hvdyBcImNvbnN0YW50XCIg4ouEIDF94o2fNCAwLCB74oCiU2hvdyBcImNvbnN1bWVcIiDii4Qg8J2VqX3ijZ80IDDin6kiLCJwcmV2U2Vzc2lvbnMiOltdLCJjdXJyZW50U2Vzc2lvbiI6eyJjZWxscyI6W10sImNyZWF0ZWRBdCI6MTY3MjE5NjY2MjcxOH0sImN1cnJlbnRDZWxsIjp7ImZyb20iOjAsInRvIjo4OCwicmVzdWx0IjpudWxsfX0%3D)
