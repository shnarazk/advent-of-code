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

let area (x1, y1) (x2, y2) : int =
  let w = abs (x1 - x2 + 1) and h = abs (y1 - y2 + 1) in
  w * h

let solve1 (points : (int * int) array) : int =
  let len = Array.length points and value = ref 0 in
  for i = 0 to len - 1 do
    let p = points.(i) in
    for j = i + 1 to len - 1 do
      let q = points.(j) in
      let a = area p q in
      if !value < a then value := a
    done
  done;
  !value

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: (int * int) array] data;
  let part1 = solve1 data and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
