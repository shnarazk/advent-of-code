open Angstrom
open Eio

let token = take_while (function 'A' .. 'z' -> true | _ -> false)

let parse_line =
  lift2 (fun h t -> (h, t)) (token <* string ": ") (Aoc.Parsers.separated token (char ' '))

let parser = Aoc.Parsers.separated parse_line (char '\n')

(* for Advent of Code 2025 *)
let () =
  Eio_main.run @@ fun env ->
  let stdout = Stdenv.stdout env
  and fs = Stdenv.fs env
  and aoc_dir =
    match Sys.getenv_opt "AOC_DIR" with
    | Some dir -> dir
    | None -> failwith "AOC_DIR is not defined"
  in
  let data_file = Path.(fs / aoc_dir / "data/2025/input-day11.txt") in
  Flow.copy_string "\nHello, World!\n" stdout;
  Flow.copy_string ("AOC_DIR: " ^ aoc_dir ^ "\n") stdout;
  Flow.copy_string (Path.native data_file |> Option.get) stdout;
  Flow.copy_string "\n" stdout;
  let data : string = Path.load data_file in
  (* Flow.copy_string data stdout; *)
  let parsed =
    match Angstrom.(parse_string ~consume:Prefix parser data) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  Flow.copy_string (Format.sprintf "%d" (snd parsed.(1) |> Array.length) ^ "\n") stdout
