Data ← ⊜□\+∵(|1 =@$⊢⊔).⊜□≠@\n.&fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day07.txt"

Split ← ⊜□≠⊙.
~~~
⍤ "Broken Split" ≅{"$" "ls"} Split @ "$ ls"
~~~

Shaper ← ↘↥0-1⊗0=@/.
~~~
⍤ "1"≅"/a" Shaper "/a"
⍤ "2"≅"/a" Shaper "//a"
⍤ "3"≅"/a" Shaper "///a"
~~~

ChangeDirectory ← (|2 ?(|2 ⍜'⊡0(|1 ⍜(⇌⊔)(|1 ⊂@/↘+1⊗1=@/.↘1));)(⍜'⊡0; ∶□Shaper⊃(|2 ⊂∶⊂∶"/"⊙(⊔⊡0))(|2 ⋅∘))≅"..".)
~~~
⍤ "Wrong CD"≅{"/var/tmp/" []} ChangeDirectory "tmp" {"/var/" []}
⍤ "Wrong CD"≅{"/var/abc/tmp/" []} ChangeDirectory "tmp" {"/var/abc/" []}
⍤ "Wrong up"≅{"/var/" []} ChangeDirectory ".." {"/var/tmp/" []}
⍤ "Should /"≅{"/" []} ChangeDirectory ".." {"/var/" []}
⍤ "Should /"≅{"/" []} ChangeDirectory ".." {"/" []}
⍤ "Should /"≅{"/" []} ChangeDirectory "/" {"/" []}
~~~

HandleCd ← |3 ChangeDirectory ⊔⊡1;∶

# dir "size file" --- {"dir/file" size}
Merger ← (|2 ⊂∩□⊃(⊂∩⊔⊙'⊡1)⋅(parse⊔⊡0)⊙(Split@ ⊔))
~~~
⍤ "Broken Merger"≅[□"/var/tmp/c.txt" □10] Merger □"/var/tmp/" □"10 c.txt"
~~~

HandleLs ← |3 ⍜'⊡1(□⊂⊔⊙(?(↯ 0_2)∘=0⧻.⊔))∶≡Merger⊏⊙∶⊃(⬚0↙∶[]⧻∘)⊙(⊡0.)⊔▽∵(¬≅"dir"⊔⊡0Split@\s⊔).↘1;
HandleCommand ← |2 ?HandleCd HandleLs ⊗0[⊃(≅"cd"⊔⊡0)(≅"ls"⊔⊡0)].↘1 Split @ ⊔⊢.⊔∶
~~~
⍤ "Broken HandleCommand cd"≅{"/tmp/" ↯0_2[]}HandleCommand [∩□"/"↯0_2[]]{"$ cd tmp"}
⍤ "Broken HandleCommand ls"≅{"/"[{"/a.txt" 344}{"/b.ua" 120}]}HandleCommand[∩□"/"↯0_2[]]{"$ ls" "344 a.txt" "120 b.ua"}
~~~

fs ← ⊔⊡1∧HandleCommand[∩□"/"↯0_2[]]Data

Dirname ← ?("/";)(↙ ⊏¯1⊚=@/.)≅1/+=@/.
~~~
⍤ "!" ≅ "/abc/def" Dirname "/abc/def/g.ua"
⍤ "!" ≅ "/" Dirname "/"
⍤ "!" ≅ "/" Dirname "/aa"
~~~

SubSeqs ← (⊂⊙□≡'□↙ ↥1∶↯⧻,∶⊚=@/..)
~~~
⍤ "!" ≅ {"/" "/abc" "/abc/def" "/abc/def/xyz"} SubSeqs "/abc/def/xyz"
~~~

Dirs ← ⊏⍏.⊝∧(|2 ⊂⊙(SubSeqs ⊔))[] ⊝≡(⍜⊔ Dirname ⊢) fs

StartsWith ← |2 ↧↥⊃⊃(=@/⬚@ ⊏)(=1)(≅⬚@\n↙)∶⊙(⧻.)
~~~
⍤ "!" StartsWith "/abc/def/g.ua" "/abc/def"
⍤ "!" StartsWith "/abc/eaf" "/abc"
⍤ "!" ¬StartsWith "/abcde/eaf" "/abc"
⍤ "!" StartsWith "/abc/def/g.ua" "/"
~~~

DepthFrom ← |2 /+=@/↘⊃⧻(⋅∘)
~~~
⍤ "!" ≅ 1 DepthFrom "/abc/def" "/abc/def/g.ua"
⍤ "!" ≅ 3 DepthFrom "/abc/def" "/abc/def/abc/x/txt.txt"
~~~

SizeOf ← (|1 /+≡(|1 ;DepthFrom⊃⊃(⊔⊡0)(⊔⊡1)(⊔⊡2))▽≡(StartsWith⊃(⊔⊡1)(⊔⊡0)).≡(⊂□∶) fs ↯⧻ fs)
# ↯ ¯1_1 Dirs
DirSizes ← ≡(⊂∶SizeOf⊔.) Dirs

&p$"Part1: _"/+≡(⊔⊡1)⊏⍏≡(⊔⊡1).▽≡(≤100000⊔⊡1).DirSizes
Threshold ← - - 30000000 70000000 SizeOf "/"
&p$"Part2: _"/↧≡(⊔⊡1)▽≡(≥Threshold⊔⊡1).DirSizes
