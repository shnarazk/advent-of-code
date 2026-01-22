open Angstrom
open Aoc
open Eio
open Format

let parse_line = lift3 (fun a _ b -> (a, b)) Parsers.integer (char ',') Parsers.integer
let parser = Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

module IntSet = Hashtbl.Make (struct
  type t = int

  let equal = ( = )
  let hash = Hashtbl.hash
end)

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

let solve2 (points : (int * int) array) : int =
  assert (Array.to_seq points |> Seq.for_all (fun (x, y) -> x > 0 && y > 0));
  let pick_x = IntSet.create 64 and pick_y = IntSet.create 64 in
  Array.to_seq points
  |> Seq.iter (fun (x, y) ->
      IntSet.replace pick_x x ();
      IntSet.replace pick_y y ());
  let pullback_x = IntSet.to_seq_keys pick_x |> Array.of_seq
  and pullback_y = IntSet.to_seq_keys pick_y |> Array.of_seq in
  Array.fast_sort compare pullback_x;
  Array.fast_sort compare pullback_y;
  print_endline @@ [%show: int array] pullback_x;
  let pushout_x = Array.to_seqi pullback_x |> Seq.map (fun (c, w) -> (w, c)) |> IntSet.of_seq
  and pushout_y = Array.to_seqi pullback_y |> Seq.map (fun (c, w) -> (w, c)) |> IntSet.of_seq in
  print_endline @@ [%show: (int * int) array] @@ Array.of_seq @@ IntSet.to_seq pushout_x;
  IntSet.length pushout_x + IntSet.length pushout_y

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: (int * int) array] data;
  let part1 = solve1 data and part2 = solve2 data in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
