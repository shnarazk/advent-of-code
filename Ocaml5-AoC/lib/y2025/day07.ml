open Angstrom
open Eio
open Format

let parse_line =
  take_while1 (function '.' | '^' | 'S' -> true | _ -> false) >>| fun (l : string) ->
  String.to_seqi l
  |> Seq.filter_map (fun (i, c) -> if c != '.' then Option.some i else Option.none)
  |> Array.of_seq

let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

module Occurrence = Hashtbl.Make (struct
  type t = int

  let equal = ( = )
  let hash = Hashtbl.hash
end)

let count (start : int Occurrence.t) (branches : int array array) : int * int =
  let state, count =
    Array.fold_left
      (fun (state, c) line ->
        Occurrence.to_seq state
        |> Seq.fold_left
             (fun (oc, c) (pos, w) ->
               if Array.exists (fun x -> x = pos) line then begin
                 Occurrence.replace oc (pos - 1)
                 @@ (Occurrence.find_opt oc (pos - 1) |> Option.fold ~none:w ~some:(fun n -> w + n));
                 Occurrence.replace oc (pos + 1)
                 @@ (Occurrence.find_opt oc (pos + 1) |> Option.fold ~none:w ~some:(fun n -> w + n));
                 (oc, c + 1)
               end
               else begin
                 Occurrence.replace oc pos
                 @@ (Occurrence.find_opt oc pos |> Option.fold ~none:w ~some:(fun n -> w + n));
                 (oc, c)
               end)
             (Occurrence.(create (length state)), c))
      (start, 0) branches
  in
  (count, Occurrence.to_seq_values state |> Seq.fold_left ( + ) 0)

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> Array.to_seq v |> Seq.filter (fun l -> Array.length l > 0) |> Array.of_seq
    | Error msg -> failwith msg
  in
  (* Flow.copy_string ([%show: int array array] data ^ "\n") stdout; *)
  let occs = Occurrence.create 10 in
  Occurrence.add occs data.(0).(0) 1;
  let data = Array.sub data 1 (Array.length data - 1) in
  let part1, part2 = count occs data in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
