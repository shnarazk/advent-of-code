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

let dist3 ((x1 : int), (y1 : int), (z1 : int)) ((x2 : int), (y2 : int), (z2 : int)) : int =
  let x = x2 - x1 and y = y2 - y1 and z = z2 - z1 in
  (x * x) + (y * y) + (z * z)

let groups1 (dists : (int * int) array) (n : int) (upto : int) : int =
  let num_groups = ref n
  and _next_group_id = ref 1
  and groups = ref [| 0 |]
  and to_group : int array = Array.make n 0 in
  let belongsTo (id : int) : int =
    let rec loop (gid : int) : int =
      match !groups.(gid) with 0 -> gid | _ -> loop !groups.(gid)
    in
    loop to_group.(id)
  in
  for i = 0 to upto do
    let p1, p2 = dists.(i) in
    let p1_group = belongsTo p1 and p2_group = belongsTo p2 in
    match (p1_group, p2_group) with
    | 0, 0 ->
        num_groups := !num_groups + 1;
        ()
    | _g, 0 -> ()
    | 0, _g -> ()
    | g1, g2 ->
        if g1 = g2 then ()
        else (
          num_groups := !num_groups - 1;
          ())
  done;
  0

let groups2 (_dists : (int * int) array) (_n : int) : int = 0

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: (int * int * int) array] data;
  let dists = Dist.create 64 in
  Array.to_seqi data
  |> Seq.iter (fun (i, p1) ->
      Array.to_seqi data
      |> Seq.iter (fun (j, p2) -> if i < j then Dist.add dists (dist3 p1 p2) (i, j)));
  let dists = Array.of_seq @@ Dist.to_seq dists in
  Array.fast_sort (fun (a, _) (b, _) -> compare a b) dists;
  print_endline @@ [%show: (int * (int * int)) array] dists;
  let dists = Array.map (fun (_, p) -> p) dists in
  let num_nodes = Array.length data in
  let part1_limit = if num_nodes == 20 then 10 else 100 in
  let part1 = groups1 dists num_nodes part1_limit and part2 = groups2 dists num_nodes in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
