open Angstrom
open Eio
open Format

let parse_line = Aoc.Parsers.separated Aoc.Parsers.integer (char '-') >>| fun v -> (v.(0), v.(1))
let parser = Aoc.Parsers.separated parse_line (char ',') <* end_of_line <* end_of_input

let pick (n : int) (_width : int) (_ith : int) : int =
  let digits = Aoc.Number.digits n in
  print_endline @@ [%show: int list] digits;
  0

let repeat (n : int) (k : int) : int =
  let width = List.length @@ Aoc.Number.digits n in
  Seq.ints 0 |> Seq.take k |> Seq.fold_left (fun acc _ -> Aoc.Number.int_pow (acc * 10) width + n) 0

let solve1 ((b, e) : int * int) : int = e - b
let solve2 ((b, e) : int * int) : int = e - b

let solve data_file stdout =
  let data =
    match parse_string ~consume:All parser @@ Path.load data_file with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: (int * int) array] data;
  let part1 = Array.to_seq data |> Seq.map solve1 |> Seq.fold_left ( + ) 0
  and part2 = Array.to_seq data |> Seq.map solve2 |> Seq.fold_left ( + ) 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
