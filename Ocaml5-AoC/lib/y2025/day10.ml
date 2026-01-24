open Angstrom
open Aoc
open Eio
open Format

let parse_indicator =
  char '['
  *> ( take_while1 (function '.' | '#' -> true | _ -> false) >>| fun s ->
       String.to_seq s |> Seq.map (fun ch -> ch = '#') |> Array.of_seq )
  <* string "] "

let parse_button = char '(' *> Parsers.separated Parsers.integer (char ',') <* string ") "
let parse_buttons = many1 parse_button
let parse_goal = char '{' *> Parsers.separated Parsers.integer (char ',') <* char '}'
let parse_line = lift3 (fun a b c -> (a, b, c)) parse_indicator parse_buttons parse_goal
let parser = Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

(* module Dist = Hashtbl.Make (struct
  type t = 

  let equal a b = 
  let hash = Hashtbl.hash
end)
*)

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:Prefix parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: (bool array * int array list * int array) array] data;
  let part1 = 0 and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
