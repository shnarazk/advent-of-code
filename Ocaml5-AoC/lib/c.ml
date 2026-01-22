(* combinators *)

let both (f : 'a -> 'b) (x : 'a) (y : 'a) : 'b * 'b = (f x, f y)
let swap (x : 'a) (y : 'b) : 'b * 'a = (y, x)
let uncurry (f : 'a -> 'b -> 'c) (x : 'a * 'b) : 'c = f (fst x) (snd x)
let k (x : 'a) (_ : 'b) : 'a = x
let before (f : 'a -> 'b) (x : 'a) : 'b * 'a = (f x, x)
let after (f : 'a -> 'b) (x : 'a) : 'a * 'b = (x, f x)
