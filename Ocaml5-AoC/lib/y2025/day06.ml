open Angstrom
open Aoc
open Eio
open Format

let parse_op = char '+' <|> char '*'
let whitespaces0 = take_while (fun c -> c = ' ')
let whitespaces1 = take_while1 (fun c -> c = ' ')
let parse_numbers = whitespaces0 *> Parsers.separated Parsers.integer whitespaces1 <* whitespaces0
let parse_ops = Parsers.separated parse_op whitespaces1 <* whitespaces0

let parser =
  lift2
    (fun a b -> (a, b))
    (Parsers.separated parse_numbers end_of_line <* end_of_line)
    (parse_ops <* end_of_line <* end_of_input)

(* module Dist = Hashtbl.Make (struct
  type t =

  let equal a b =
  let hash = Hashtbl.hash
end)
*)
let rec shape (l : string list) : string list list =
  match List.find_index (fun s -> String.for_all (fun c -> c = ' ') s) l with
  | None -> [ l ]
  | Some n -> List.(append [ take n l ] (shape (List.drop (n + 1) l)))

let solve data_file stdout =
  let input = Path.load data_file in
  let data, ops =
    match Angstrom.(parse_string ~consume:All parser @@ input) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  let nums0 =
    Array.to_seq data |> Seq.map Array.to_seq |> Seq.transpose |> Seq.map Array.of_seq
    |> Array.of_seq
  in
  (* print_endline @@ [%show: int array array] data; *)
  (* print_endline @@ [%show: char array] ops; *)
  let nums90 =
    String.map (fun c -> if c = '+' || c = '*' then ' ' else c) input
    |> String.split_on_char '\n' |> List.to_seq |> Seq.map String.to_seq |> Seq.transpose
    |> Seq.map String.of_seq |> List.of_seq |> shape
    |> List.map (fun l ->
        List.map
          (fun s ->
            Angstrom.(parse_string ~consume:All Parsers.integer (String.trim s)) |> Result.get_ok)
          l)
    |> List.map Array.of_list |> Array.of_list
  in
  (* print_endline @@ [%show: int array array] nums0; *)
  (* print_endline @@ [%show: int array array] nums90; *)
  (* print_endline @@ [%show: int array] data; *)
  let part1 =
    Array.to_seqi ops
    |> Seq.map (fun (i, op) ->
        if op = '+' then Array.to_seq nums0.(i) |> Seq.fold_left ( + ) 0
        else Array.to_seq nums0.(i) |> Seq.fold_left ( * ) 1)
    |> Seq.fold_left ( + ) 0
  and part2 =
    Array.to_seqi ops
    |> Seq.map (fun (i, op) ->
        if op = '+' then Array.to_seq nums90.(i) |> Seq.fold_left ( + ) 0
        else Array.to_seq nums90.(i) |> Seq.fold_left ( * ) 1)
    |> Seq.fold_left ( + ) 0
  in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
