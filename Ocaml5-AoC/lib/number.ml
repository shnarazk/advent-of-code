(** make a list of digit from an int *)
let digits (n : int) : int list =
  let rec loop (n : int) : int list =
    match n with 0 -> [] | _ -> List.append (loop (n / 10)) [ n mod 10 ]
  in
  match n with 0 -> [ 0 ] | _ -> loop n

let rec int_pow (a : int) (b : int) =
  match b with
  | 0 -> 1
  | 1 -> a
  | _ when b > 0 -> a * int_pow a (b - 1)
  | _ -> invalid_arg "negative power"
