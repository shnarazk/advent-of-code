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
  let part1 = 0 and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
