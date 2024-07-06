Factor always crashes after the first(?) gc on M1. I gave up for now.

# 2024-07-07

Here's the patch to run:

```diff
--- a/Factor/test.factor
+++ b/Factor/test.factor
@@ -16,24 +16,23 @@ IN: test

 : transform ( substring -- letter )
   {
-    { [ dup 0 "one"   swapd subseq-starts-at? ] [ drop CHAR: 1 ] }
-    { [ dup 0 "two"   swapd subseq-starts-at? ] [ drop CHAR: 2 ] }
-    { [ dup 0 "three" swapd subseq-starts-at? ] [ drop CHAR: 3 ] }
-    { [ dup 0 "four"  swapd subseq-starts-at? ] [ drop CHAR: 4 ] }
-    { [ dup 0 "five"  swapd subseq-starts-at? ] [ drop CHAR: 5 ] }
-    { [ dup 0 "six"   swapd subseq-starts-at? ] [ drop CHAR: 6 ] }
-    { [ dup 0 "seven" swapd subseq-starts-at? ] [ drop CHAR: 7 ] }
-    { [ dup 0 "eight" swapd subseq-starts-at? ] [ drop CHAR: 8 ] }
-    { [ dup 0 "nine"  swapd subseq-starts-at? ] [ drop CHAR: 9 ] }
+    { [ dup "" = ] [ drop CHAR: A ] }
+    { [ dup " " append 0 "one"   swapd subseq-starts-at? ] [ drop CHAR: 1 ] }
+    { [ dup " " append 0 "two"   swapd subseq-starts-at? ] [ drop CHAR: 2 ] }
+    { [ dup " " append 0 "three" swapd subseq-starts-at? ] [ drop CHAR: 3 ] }
+    { [ dup " " append 0 "four"  swapd subseq-starts-at? ] [ drop CHAR: 4 ] }
+    { [ dup " " append 0 "five"  swapd subseq-starts-at? ] [ drop CHAR: 5 ] }
+    { [ dup " " append 0 "six"   swapd subseq-starts-at? ] [ drop CHAR: 6 ] }
+    { [ dup " " append 0 "seven" swapd subseq-starts-at? ] [ drop CHAR: 7 ] }
+    { [ dup " " append 0 "eight" swapd subseq-starts-at? ] [ drop CHAR: 8 ] }
+    { [ dup " " append 0 "nine"  swapd subseq-starts-at? ] [ drop CHAR: 9 ] }
     [ first ]
   }
   cond
 ;
```
