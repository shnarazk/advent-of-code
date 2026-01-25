open Angstrom
open Aoc
open Eio
open Format

let token = take_while1 (function 'A' .. 'z' -> true | _ -> false)
let parse_line = Parsers.separated token (char ' ')

let parse_block =
  let id = Parsers.integer <* string ":\n" in
  lift2 (fun a b -> (a, b)) id @@ Parsers.separated (many1 (char '.' <|> char '#')) end_of_line

let parse_blocks = many1 (parse_block <* (end_of_line <* end_of_line))
let parse_size = lift3 (fun a _ b -> (a, b)) Parsers.integer (char 'x') Parsers.integer

let parse_config =
  lift2
    (fun a b -> (a, b))
    (parse_size <* string ": ")
    (Parsers.separated Parsers.integer (char ' '))

let parse_configs = Parsers.separated parse_config end_of_line
let parser = lift2 (fun a b -> (a, b)) parse_blocks (parse_configs <* end_of_line)

(* module Dist = Hashtbl.Make (struct
  type t = 

  let equal a b = 
  let hash = Hashtbl.hash
end)
*)

let solve data_file stdout =
  let blocks, configs =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: (int * char list array) list] blocks;
  print_endline @@ [%show: ((int * int) * int array) array] configs;
  let part1 = 0 and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
