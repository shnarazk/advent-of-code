open Angstrom
open Eio
open Format

let parse_line =
  take_while1 (function '.' | '@' -> true | _ -> false) >>| fun l ->
  String.to_seqi l
  |> Seq.filter_map (fun (i, c) -> if c = '@' then Option.some i else Option.none)
  |> Array.of_seq

let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

type position = int * int

let add (ay, ax) (by, bx) = (ay + by, ax + bx)
let lt (ay, ax) (by, bx) = ay < by && ax < bx

(** set of 2D position *)
module Cell = Hashtbl.Make (struct
  type t = position

  let equal (ay, ax) (by, bx) = ay = by && ax = bx
  let hash = Hashtbl.hash
end)

(** 8 neighbors *)
let dirs = [| (-1, 0); (0, 1); (1, 0); (0, -1); (-1, 1); (1, 1); (1, -1); (-1, -1) |]

let depends (grid : unit Cell.t) (pos : position) : position list =
  Array.to_seq dirs |> Seq.map (fun d -> add pos d) |> Seq.filter (Cell.mem grid) |> List.of_seq

let removable (grid : unit Cell.t) (pos : position) : bool =
  Array.to_seq dirs |> Seq.map (fun d -> add pos d) |> Seq.filter (Cell.mem grid) |> Seq.length
  |> fun n -> n < 4

let solve1 (grid : unit Cell.t) : int =
  Cell.to_seq_keys grid |> Seq.filter (removable grid) |> Seq.length

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  (* print_endline @@ [%show: int array array] data; *)
  let grid = Cell.create 100 in
  Array.(iteri (fun i xs -> iter (fun j -> Cell.add grid (i, j) ()) xs) data);
  (* print_endline @@ [%show: (int * int) list] @@ Cell.to_list !grid; *)
  let part1 = solve1 grid and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
