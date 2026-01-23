(* 2 dimentional vector library *)

type dim2 = int * int

let add ((y1, x1) : dim2) ((y2, x2) : dim2) : dim2 = (y1 + y2, x1 + x2)
let eq ((y1, x1) : dim2) ((y2, x2) : dim2) : bool = y1 = y2 && x1 = x2
let le ((y1, x1) : dim2) ((y2, x2) : dim2) : bool = y1 <= y2 && x1 <= x2
let lt ((y1, x1) : dim2) ((y2, x2) : dim2) : bool = y1 < y2 && x1 < x2

let cmp ((y1, x1) : dim2) ((y2, x2) : dim2) : int =
  match compare y1 y2 with 0 -> compare x1 x2 | c -> c

(** 4 neighbors *)
let dir4 : dim2 array = [| (-1, 0); (0, 1); (1, 0); (0, -1) |]

(** 8 neighbors *)
let dir8 : dim2 array = [| (-1, 0); (-1, 1); (0, 1); (1, 1); (1, 0); (1, -1); (0, -1); (-1, -1) |]

(** note: limit is not included *)
let neightbor4 (pos : dim2) (upto : dim2) : dim2 array =
  Array.to_seq dir4
  |> Seq.map (fun d -> add pos d)
  |> Seq.filter (fun p -> le (0, 0) p && lt p upto)
  |> Array.of_seq

module Dim2Set = Hashtbl.Make (struct
  type t = dim2

  let equal = eq
  let hash = Hashtbl.hash
end)

let makeArray (h : int) (w : int) (default : 'a) : 'a array array =
  let makeVector (n : int) : 'a array = Array.make n default in
  Seq.init h (fun n -> n) |> Seq.map (fun _ -> makeVector w) |> Array.of_seq
