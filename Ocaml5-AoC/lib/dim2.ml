(* 2 dimentional vector library *)

type dim2 = int * int

let add ((y1, x1) : dim2) ((y2, x2) : dim2) : dim2 = (y1 + y2, x1 + x2)
let le ((y1, x1) : dim2) ((y2, x2) : dim2) : bool = y1 <= y2 && x1 <= x2

(** 4 neighbors *)
let dir4 : dim2 array = [| (-1, 0); (0, 1); (1, 0); (0, -1) |]

(** 8 neighbors *)
let dir8 : dim2 array = [| (-1, 0); (-1, 1); (0, 1); (1, 1); (1, 0); (1, -1); (0, -1); (-1, -1) |]

(** note: limit is included *)
let neightbor4 (pos : dim2) (upto : dim2) : dim2 array =
  Array.to_seq dir4
  |> Seq.map (fun d -> add pos d)
  |> Seq.filter (fun p -> le (0, 0) p && le p upto)
  |> Array.of_seq
