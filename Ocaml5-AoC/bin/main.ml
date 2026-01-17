open Eio
open Format

let year = ref 2025
let day = ref 1
let help_msg = "aoc [-y YEAR] day"
let spec_lst = [ ("-y", Arg.Set_int year, sprintf "year (default: %d)" !year) ]
let () = Arg.parse spec_lst (fun d -> day := int_of_string d) help_msg

let aoc_dir =
  match Sys.getenv_opt "AOC_DIR" with Some dir -> dir | None -> failwith "AOC_DIR is not defined"

let () =
  Eio_main.run @@ fun env ->
  let stdout = Stdenv.stdout env and fs = Stdenv.fs env in
  let data_file = Path.(fs / aoc_dir / sprintf "data/%d/input-day%02d.txt" !year !day) in
  if Path.is_file data_file then
    Flow.copy_string ((Path.native data_file |> Option.get) ^ "\n") stdout
  else failwith @@ sprintf "%s does not exist." (Path.native data_file |> Option.get);
  let solver =
    match !year with
    | 2025 -> (
        match !day with
        | 03 -> Y2025.Day03.solve data_file
        | 07 -> Y2025.Day07.solve data_file
        | 11 -> Y2025.Day11.solve data_file
        | _ -> failwith "invalid day")
    | _ -> failwith "invalid year"
  in
  solver stdout
