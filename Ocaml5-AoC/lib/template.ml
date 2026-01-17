(* open Angstrom
open Eio
open Format

let token = take_while1 (function 'A' .. 'z' -> true | _ -> false)
let parse_line = Aoc.Parsers.separated token (char ' ')
let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

(* module Dist = Hashtbl.Make (struct
  type t = 

  let equal a b = 
  let hash = Hashtbl.hash
end)
*)

let solve data_file stdout =
  let _data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  let part1 = 0 and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
*)
