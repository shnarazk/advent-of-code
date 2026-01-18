let uchars_of_string (s : string) : Uchar.t array =
  let decoder = Uutf.decoder ~encoding:`UTF_8 (`String s) in
  let rec loop acc =
    match Uutf.decode decoder with
    | `Uchar u -> loop (u :: acc)
    | `End -> Array.of_list (List.rev acc)
    | `Malformed _ ->
        (* Decide how you want to handle malformed UTF-8 *)
        loop acc
    | `Await -> assert false
  in
  loop []

(** convert a UChar to a string:
print_endline (string_of_uchar (Uchar.of_int 0x1F600))
*)
let string_of_uchar (u : Uchar.t) : string =
  let buf = Buffer.create 4 in
  let encoder = Uutf.encoder `UTF_8 (`Buffer buf) in
  let _ = Uutf.encode encoder (`Uchar u) in
  let _ = Uutf.encode encoder `End in
  Buffer.contents buf
