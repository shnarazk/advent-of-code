open Angstrom
open Eio
open Format

let sign = char 'L' <|> char 'R'
let parse_line = lift2 (fun s n -> if s = 'L' then -n else n) sign Aoc.Parsers.integer
let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input
let solve1 (_turns : int array) : int = 0
let solve2 (_turns : int array) : int = 0

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: int array] data;
  let part1 = solve1 data and part2 = solve2 data in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
