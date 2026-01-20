open Angstrom
open Aoc
open Eio
open Format

let parse_line = lift3 (fun a _ b -> (a, b)) Parsers.integer (char ',') Parsers.integer
let parser = Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

(* module Dist = Hashtbl.Make (struct
  type t = 

  let equal a b = 
  let hash = Hashtbl.hash
end)
*)

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: (int * int) array] data;
  let part1 = 0 and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
