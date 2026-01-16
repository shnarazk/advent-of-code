open Angstrom

let integer = take_while1 (function '0' .. '9' -> true | _ -> false) >>| int_of_string

let separated parser separator =
  let rec go acc =
    lift2 (fun _ value -> Array.append acc [| value |]) separator parser >>= go <|> return acc
  in
  parser >>= fun init -> go [| init |]
