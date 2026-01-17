open Angstrom
open Eio
open Format

let digits =
  take_while1 (function '0' .. '9' -> true | _ -> false) >>| fun (v : string) ->
  String.to_seq v |> Seq.map (fun ch -> Char.code ch - Char.code '0') |> Array.of_seq

let parser = Aoc.Parsers.separated digits end_of_line <* end_of_line <* end_of_input

(** solve the unit problem *)
let evaluate (len : int) (a : int array) : int =
  let buffer = Array.(sub a (length a - len) len) in
  for i = Array.length a - len - 1 downto 0 do
    let target = ref a.(i) in
    let j = ref 0 in
    while !j < Array.length buffer && buffer.(!j) <= !target do
      let tmp = buffer.(!j) in
      buffer.(!j) <- !target;
      target := tmp;
      j := !j + 1
    done
  done;
  Array.fold_left (fun acc n -> (acc * 10) + n) 0 buffer

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:All parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  let part1 = Array.map (evaluate 2) data |> Array.fold_left ( + ) 0
  and part2 = Array.map (evaluate 12) data |> Array.fold_left ( + ) 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
