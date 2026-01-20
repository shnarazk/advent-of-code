open Angstrom
open Aoc
open Eio
open Format

let parse_line1 = lift3 (fun a _ b -> (a, b)) Parsers.integer (char '-') Parsers.integer
let parse_block1 = Aoc.Parsers.separated parse_line1 end_of_line
let parse_block2 = Aoc.Parsers.separated Parsers.integer end_of_line

let parser =
  lift4 (fun a _ b _ -> (a, b)) parse_block1 (count 2 end_of_line) parse_block2 end_of_line

module Level = Hashtbl.Make (struct
  type t = int * bool

  let equal = ( = )
  let hash = Hashtbl.hash
end)

let solve1 (ranges : (int * int) array) (n : int) : int =
  Array.to_seq ranges
  |> Seq.find (fun (b, e) -> b <= n && n <= e)
  |> Option.fold ~none:0 ~some:(fun _ -> 1)

let solve2 (ranges : (int * int) array) : int =
  let level = Level.create 64 in
  Array.to_seq ranges
  |> Seq.iter (fun (b, e) ->
      Level.replace level (b, false)
      @@ Option.fold ~none:1 ~some:(fun l -> l + 1)
      @@ Level.find_opt level (b, false);
      Level.replace level (e, true)
      @@ Option.fold ~none:(-1) ~some:(fun l -> l - 1)
      @@ Level.find_opt level (e, true));
  let level =
    List.fast_sort (fun (a, b1) (b, b2) -> match compare a b with 0 -> compare b1 b2 | c -> c)
    @@ List.of_seq @@ Level.to_seq level
  in
  (* print_endline @@ [%show: (int * int) list] level; *)
  List.fold_left
    (fun (sum, level, start) ((pos, _), diff) ->
      let l = level + diff in
      assert (l >= 0);
      let sum = if level > 0 && l = 0 then sum + (pos - start + 1) else sum
      and start = if level = 0 && l > 0 then pos else start in
      (sum, l, start))
    (0, 0, 0) level
  |> fun (a, l, _) ->
  assert (l = 0);
  a

let solve data_file stdout =
  let ranges, data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  (* print_endline @@ [%show: (int * int) array] ranges; *)
  (* print_endline @@ [%show: int array] data; *)
  let part1 = Array.to_seq data |> Seq.map (solve1 ranges) |> Seq.fold_left ( + ) 0
  and part2 = solve2 ranges in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
