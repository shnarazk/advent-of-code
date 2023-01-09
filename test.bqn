#!/usr/bin/env cbqn
⟨color,term⟩ ← •Import "bqn/lib.bqn"
# •Out (color.red color.Out "hello, ")∾(color.green color.Out "hello, ")

•Out ((0 color.RGB 88‿100‿200) color.Out "hello, ")∾(color.green color.Out "hello, ")
•Out ((200‿220‿189 color.RGB 0) color.Out "hello, ")∾(color.green color.Out "hello, ")
•Out (30‿30‿10 color.RGB 188‿140‿200) color.Out "hello, world!"
•Out "line 1 --------------"
•Out "line 2 --------------"
•Out "line 3 --------------"
•Out (term.Revert 3)∾color.red color.Out "line 1"
•Out color.red color.Out "line 2"
•Out color.red color.Out "line 3"

term.Outln "ok"
# term.Print ⟨3⟩
# term.Outln "ok"
•Show ⟨3⟩
term.Outln "ok"
color.green term.Print ⟨3⟩
color.red term.Println ⟨3⟩
