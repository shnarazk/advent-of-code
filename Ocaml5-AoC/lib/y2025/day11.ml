open Angstrom
open Eio
open Format

let token = take_while (function 'A' .. 'z' -> true | _ -> false)

let parse_line =
  lift2 (fun h t -> (h, t)) (token <* string ": ") (Aoc.Parsers.separated token (char ' '))

let parser = Aoc.Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

module Dist = Hashtbl.Make (struct
  type t = string * string

  let equal a b = String.equal (fst a) (fst b) && String.equal (snd a) (snd b)
  let hash = Hashtbl.hash
end)

(* We use -1 for neighbor nodes. So We have to covert this value to real value if needed *)
let rec count_paths dist src dst =
  match Dist.find_opt dist (src, dst) with
  | Some d -> abs d
  | None ->
      let count = ref 0 in
      Dist.iter
        (fun sd n ->
          if fst sd = src && n = -1 then count := !count + count_paths dist (snd sd) dst else ())
        dist;
      Dist.add dist (src, dst) !count;
      !count

let solve data_file stdout =
  let data : string = Path.load data_file in
  (* Flow.copy_string data stdout; *)
  let parsed =
    match Angstrom.(parse_string ~consume:All parser data) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  let flow : int Dist.t = Dist.create 16 in
  Array.iter
    (fun setting -> Array.iter (fun dest -> Dist.add flow (fst setting, dest) (-1)) (snd setting))
    parsed;
  Flow.copy_string (sprintf "Part1: %d\n" (count_paths flow "you" "out")) stdout;
  let dac_fft = count_paths flow "dac" "fft" in
  let fft_dac = count_paths flow "fft" "dac" in
  let part2 =
    if dac_fft > 0 then dac_fft * count_paths flow "svr" "dac" * count_paths flow "fft" "out"
    else fft_dac * count_paths flow "svr" "fft" * count_paths flow "dac" "out"
  in
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
