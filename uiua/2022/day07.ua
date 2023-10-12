Data ← ⊜□\+∵(|1 =@$⊢⊔).⊜□≠@\n.&fras⊂&var"AOC_REPO_DIR" "/data/2022/input-day07.txt"
Split ← ⊜□≠⊙.
Shaper ← ↘↥0-1⊗0=@/.
~~~
⍤ "1"≅"/a"Shaper "/a"
⍤ "2"≅"/a"Shaper "//a"
⍤ "3"≅"/a"Shaper "///a"
~~~

~~~
⍤ "Broken Split"≅{"$" "ls"}Split @ "$ ls"
~~~
ChangeDirectory ← |2 ?(|2 ⍜'⊡0(|1 ⍜(⇌⊔)(|1 ⊂@/↘+1⊗1=@/.↘1));)(⍜'⊡0; ∶□Shaper⊃(|2 ⊂∶⊂∶"/"⊙(⊔⊡0))(|2 ⋅∘))≅"..".
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
Join ← ?(⋅⋅∘)(?(∘⊙;)(⊂))⊃∩(=0⧻)⊙∘ # `?` require two identical signature functions
~~~
⍤ "polymorphic join"≅[1_2 5_6]Join [] [1_2 5_6]
⍤ "polymorphic join"≅[1_2 5_6]Join [1_2 5_6][]
⍤ "polymorphic join"≅[1_2 5_6 2_3]Join [1_2 5_6][2_3]
~~~
HandleLs ← |3 ⍜'⊡1(□Join⊔⊙⊔)∶≡Merger ⊏ ⊙∶⊃(⬚0↙∶[]⧻∘)⊙(⊡0.)⊔▽∵(¬≅"dir"⊔⊡0Split@ ⊔).↘1;
# HandleLs ← |3 ⍜'⊡1'∘; ∶□≡Merger ⊏ ⊙∶⊃(⬚0↙∶[]⧻∘)⊙(⊡0.)⊔▽∵(¬≅"dir"⊔⊡0Split@ ⊔).↘1;
HandleCommand ← |2 ?HandleCd HandleLs ⊗0[⊃(≅"cd"⊔⊡0)(≅"ls"⊔⊡0)].↘1 Split @ ⊔⊢.⊔∶
~~~
⍤ "Broken HandleCommand cd"≅{"/tmp/" []}HandleCommand [∩□"/"[]]{"$ cd tmp"}
⍤ "Broken HandleCommand ls"≅{"/"[{"/a.txt" 344}{"/b.ua" 120}]}HandleCommand[∩□"/"[]]{"$ ls" "344 a.txt" "120 b.ua"}
~~~
fs ← ⊔⊡1∧HandleCommand[∩□"/"[]]Data
Dirname ← ?(∘)(↙ ⊏¯1⊚=@/.)≅"/".
~~~
⍤ "!" ≅ dump∘"/abc/def" Dirname "/abc/def/g.ua"
⍤ "!" ≅ dump∘"/" Dirname "/"
~~~
dirs ← ⊝≡(⍜⊔ Dirname ⊢) fs
