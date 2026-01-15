open Eio

let () =
  Eio_main.run @@ fun env ->
  let stdout = Stdenv.stdout env
  and fs = Stdenv.fs env
  and aoc_dir = match Sys.getenv_opt "AOC_DIR" with
  | Some dir -> dir
  | None -> failwith "AOC_DIR is not defined" in
  let data_file = Path.(fs / aoc_dir / "data/2025/input-day11.txt") in
  Flow.copy_string "\nHello, World!\n" stdout;
  Flow.copy_string ("AOC_DIR: " ^ aoc_dir ^ "\n") stdout;
  Flow.copy_string (Path.native data_file |> Option.get) stdout;
  let data : string = Path.load data_file in
  Flow.copy_string data stdout;
