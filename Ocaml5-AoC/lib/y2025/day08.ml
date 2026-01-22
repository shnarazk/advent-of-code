open Angstrom
open Aoc
open Eio
open Format

let parse_line = Parsers.separated Parsers.integer (char ',') >>| fun l -> (l.(0), l.(1), l.(2))
let parser = Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

module Dist = Hashtbl.Make (struct
  type t = int

  let equal = ( = )
  let hash = Hashtbl.hash
end)

module GroupSize = Hashtbl.Make (struct
  type t = int

  let equal = ( = )
  let hash = Hashtbl.hash
end)

let dist3 ((x1 : int), (y1 : int), (z1 : int)) ((x2 : int), (y2 : int), (z2 : int)) : int =
  let x = x2 - x1 and y = y2 - y1 and z = z2 - z1 in
  (x * x) + (y * y) + (z * z)

let groups1 (dists : (int * int) array) (n : int) (upto : int) : int =
  let num_groups = ref n
  and next_group_id = ref 1
  and groups = ref [| 0 |]
  (* from id to group id *)
  and to_group : int array = Array.make n 0 in
  let belongsTo (id : int) : int =
    let rec loop (gid : int) : int =
      let meta = !groups.(gid) in
      match meta with 0 -> gid | _ -> loop meta
    in
    loop to_group.(id)
  in
  for i = 0 to upto - 1 do
    let p1, p2 = dists.(i) in
    match (belongsTo p1, belongsTo p2) with
    | 0, 0 ->
        num_groups := !num_groups + 1;
        to_group.(p1) <- !next_group_id;
        to_group.(p2) <- !next_group_id;
        assert (Array.length !groups = !next_group_id);
        groups := Array.append !groups [| 0 |];
        next_group_id := !next_group_id + 1
    | 0, g -> to_group.(p1) <- g
    | g, 0 -> to_group.(p2) <- g
    | g1, g2 ->
        if g1 != g2 then (
          let l = min g1 g2 and m = max g1 g2 in
          assert (l != 0);
          !groups.(l) <- m;
          num_groups := !num_groups - 1)
  done;
  let group_of = Array.init n belongsTo and group_size = GroupSize.create !num_groups in
  Array.to_seq group_of
  |> Seq.iter (fun k ->
      if k > 0 then
        GroupSize.replace group_size k
        @@ Option.fold ~none:1 ~some:(fun n -> n + 1)
        @@ GroupSize.find_opt group_size k);
  let s = GroupSize.to_seq_values group_size |> Array.of_seq in
  Array.fast_sort (fun a b -> compare b a) s;
  Array.to_seq s |> Seq.take 3 |> Seq.fold_left ( * ) 1

let groups2 (dists : (int * int) array) (data : (int * int * int) array) : int =
  let n = Array.length data in
  let num_groups = ref n
  and next_group_id = ref 1
  and groups = ref [| 0 |]
  (* from id to group id *)
  and to_group : int array = Array.make n 0 in
  let belongsTo (id : int) : int =
    let rec loop (gid : int) : int =
      let meta = !groups.(gid) in
      match meta with 0 -> gid | _ -> loop meta
    in
    loop to_group.(id)
  in
  let unconverged (_ : unit) =
    let g = belongsTo 0 in
    to_group.(0) = 0 || not Seq.(ints 1 |> take (n - 1) |> for_all (fun i -> belongsTo i = g))
  in
  let i = ref 0 in
  while unconverged () do
    let p1, p2 = dists.(!i) in
    i := !i + 1;
    match (belongsTo p1, belongsTo p2) with
    | 0, 0 ->
        num_groups := !num_groups + 1;
        to_group.(p1) <- !next_group_id;
        to_group.(p2) <- !next_group_id;
        assert (Array.length !groups = !next_group_id);
        groups := Array.append !groups [| 0 |];
        next_group_id := !next_group_id + 1
    | 0, g -> to_group.(p1) <- g
    | g, 0 -> to_group.(p2) <- g
    | g1, g2 ->
        if g1 != g2 then (
          let l = min g1 g2 and m = max g1 g2 in
          assert (l != 0);
          !groups.(l) <- m;
          num_groups := !num_groups - 1)
  done;
  let p, q = dists.(!i - 1) in
  print_endline @@ [%show: int * int] (p, q);
  (fun (a, _, _) (b, _, _) -> a * b) data.(p) data.(q)

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  let dists = Dist.create 64 in
  Array.to_seqi data
  |> Seq.iter (fun (i, p1) ->
      Array.to_seqi data
      |> Seq.iter (fun (j, p2) -> if i < j then Dist.add dists (dist3 p1 p2) (i, j)));
  let dists = Array.of_seq @@ Dist.to_seq dists in
  Array.fast_sort (fun (a, _) (b, _) -> compare a b) dists;
  let dists = Array.map (fun (_, p) -> p) dists in
  let num_nodes = Array.length data in
  let part1_limit = if num_nodes == 20 then 10 else 1000 in
  let part1 = groups1 dists num_nodes part1_limit and part2 = groups2 dists data in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
