open Angstrom
open Eio
open Format

let parse_line = take_while (function '.' | '^' | 'S' -> true | _ -> false)
let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_input

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  Flow.copy_string ([%show: string array] data) stdout;
  Flow.copy_string (sprintf "Part1: %d\n" 0) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" 0) stdout
