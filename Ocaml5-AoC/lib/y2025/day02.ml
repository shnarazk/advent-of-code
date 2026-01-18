open Angstrom
open Eio
open Format

let parse_line = Aoc.Parsers.separated Aoc.Parsers.integer (char '-')
let parser = Aoc.Parsers.separated parse_line (char ',') <* end_of_line <* end_of_input

let solve data_file stdout =
  let data =
    match parse_string ~consume:All parser @@ Path.load data_file with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: int array array] data;
  let part1 = 0 and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
