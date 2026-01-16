open Eio

let aoc_dir =
  match Sys.getenv_opt "AOC_DIR" with Some dir -> dir | None -> failwith "AOC_DIR is not defined"

(* Flow.copy_string ("AOC_DIR: " ^ aoc_dir ^ "\n") stdout; *)

(* for Advent of Code 2025 day11 *)
let () =
  Eio_main.run @@ fun env ->
  let stdout = Stdenv.stdout env and fs = Stdenv.fs env in
  let data_file = Path.(fs / aoc_dir / "data/2025/input-day11.txt") in
  (* Flow.copy_string (Path.native data_file |> Option.get) stdout; *)
  (* Flow.copy_string "\n" stdout; *)
  Y2025.Day11.solve data_file stdout
