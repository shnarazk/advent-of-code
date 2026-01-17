open Angstrom
open Eio
open Format

let parse_line =
  take_while1 (function '.' | '@' -> true | _ -> false) >>| fun l ->
  String.to_seqi l
  |> Seq.filter_map (fun (i, c) -> if c = '@' then Option.some i else Option.none)
  |> Array.of_seq

let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

module Cell = Set.Make (struct
  type t = int * int

  let compare _a _b = 1
end)

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  print_endline @@ [%show: int array array] data;
  let part1 = 0 and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
