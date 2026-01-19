open Eio
open Format

let year = ref 2025
let day = ref 1
let alternative_input = ref ""
let help_msg = "aoc [-y YEAR] [-a LABEL] day"

let spec_lst =
  [
    ("-a", Arg.Set_string alternative_input, "alternative input label");
    ("-y", Arg.Set_int year, sprintf "year (default: %d)" !year);
  ]

let () = Arg.parse spec_lst (fun d -> day := int_of_string d) help_msg

let aoc_dir =
  match Sys.getenv_opt "AOC_DIR" with Some dir -> dir | None -> failwith "AOC_DIR is not defined"

let () =
  Eio_main.run @@ fun env ->
  let stdout = Stdenv.stdout env and fs = Stdenv.fs env in
  let data_file =
    if !alternative_input = "" then
      Path.(fs / aoc_dir / sprintf "data/%d/input-day%02d.txt" !year !day)
    else Path.(fs / aoc_dir / sprintf "data/%d/input-day%02d-%s.txt" !year !day !alternative_input)
  in
  if Path.is_file data_file then
    Flow.copy_string ((Path.native data_file |> Option.get) ^ "\n") stdout
  else failwith @@ sprintf "%s does not exist." (Path.native data_file |> Option.get);
  let solver =
    match !year with
    | 2025 -> (
        match !day with
        | 01 -> Y2025.Day01.solve data_file
        | 02 -> Y2025.Day02.solve data_file
        | 03 -> Y2025.Day03.solve data_file
        | 04 -> Y2025.Day04.solve data_file
        | 05 -> Y2025.Day05.solve data_file
        | 07 -> Y2025.Day07.solve data_file
        | 11 -> Y2025.Day11.solve data_file
        | _ -> failwith "invalid day")
    | _ -> failwith "invalid year"
  in
  solver stdout
