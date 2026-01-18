open Angstrom
open Eio
open Format

let sign = char 'L' <|> char 'R'
let parse_line = lift2 (fun s n -> if s = 'L' then -n else n) sign Aoc.Parsers.integer
let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

let solve1 (turns : int array) : int =
  Array.to_seq turns
  |> Seq.fold_left
       (fun (value, count) turn ->
         let next = (((value + turn) mod 100) + 100) mod 100 in
         let inc = if next = 0 then 1 else 0 in
         (next, count + inc))
       (50, 0)
  |> snd

let solve2 (turns : int array) : int =
  Array.to_seq turns
  |> Seq.fold_left
       (fun (value, count) turn ->
         let n = value + turn in
         let inc = (abs n / 100) + if value > 0 && n <= 0 then 1 else 0 in
         let next = ((n mod 100) + 100) mod 100 in
         (next, count + inc))
       (50, 0)
  |> snd

let solve data_file stdout =
  let data =
    match parse_string ~consume:All parser @@ Path.load data_file with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  let part1 = solve1 data and part2 = solve2 data in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
