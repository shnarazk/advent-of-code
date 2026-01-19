open Angstrom
open Aoc
open Eio
open Format

let () =
  assert (Number.int_pow 10 0 = 1);
  assert (Number.int_pow 10 1 = 10);
  assert (Number.int_pow 10 2 = 100);
  assert (Number.int_pow 2 8 = 256)

module Count = Hashtbl.Make (struct
  type t = int

  let equal = ( = )
  let hash = Hashtbl.hash
end)

let parse_line = Parsers.separated Parsers.integer (char '-') >>| fun v -> (v.(0), v.(1))
let parser = Parsers.separated parse_line (char ',') <* end_of_line <* end_of_input

(** n -> width -> ith(zero-based) *)
let pick (n : int) (width : int) (ith : int) : int =
  let len = List.length (Number.digits n) in
  (* print_endline @@ [%show: int list] [ n; len; width; ith ]; *)
  assert (len >= width * (ith + 1));
  n / Number.int_pow 10 (len - (width * (ith + 1))) mod Number.int_pow 10 width

let () =
  assert (pick 1234 1 0 = 1);
  assert (pick 1234 1 1 = 2);
  assert (pick 1234 2 0 = 12);
  assert (pick 1234 2 1 = 34);
  assert (pick 123456789 3 2 = 789)

let repeated (n : int) (k : int) : int =
  let width = List.length @@ Number.digits n in
  Seq.ints 0 |> Seq.take k |> Seq.fold_left (fun a _ -> (a * Number.int_pow 10 width) + n) 0

let () =
  assert (repeated 12 2 = 1212);
  assert (repeated 12 4 = 12121212);
  assert (repeated 1234 2 = 12341234)

let calc (from : int) (upto : int) (len : int) (results : int list Count.t) : unit =
  let e_len = List.length (Number.digits upto) in
  if e_len / len < 2 then ()
  else
    let upto = if e_len mod len > 0 then Number.int_pow 10 (e_len / len * len) - 1 else upto
    and s_len = List.length (Number.digits from) in
    let s_len, from =
      if s_len mod len > 0 then (((s_len / len) + 1) * len, Number.int_pow 10 (s_len - 1))
      else (s_len, from)
    in
    if len == 1 then
      for d = 1 to 9 do
        for l = s_len to e_len do
          let x = repeated d l in
          if from <= x && x <= upto then
            Count.replace results x
            @@ (Count.find_opt results x |> Option.fold ~none:[ l ] ~some:(fun lst -> l :: lst))
        done
      done
    else
      for d = pick from len 0 to pick upto len 0 do
        let repeat = s_len / len in
        let x = repeated d repeat in
        if from <= x && x <= upto then
          Count.replace results x
          @@ (Count.find_opt results x |> Option.fold ~none:[ repeat ] ~some:(fun l -> repeat :: l))
      done

let solve data_file stdout =
  let data =
    match parse_string ~consume:All parser (Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  and part1 = ref 0
  and part2 = ref 0 in
  (* print_endline @@ [%show: (int * int) array] data; *)
  Array.to_seq data
  |> Seq.iter (fun (b, e) ->
      let results = Count.create 10 in
      for l = 1 to 12 do
        calc b e l results
      done;
      (* print_endline @@ [%show: (int * int list) list] (Count.to_seq results |> List.of_seq); *)
      Count.to_seq results
      |> Seq.iter (fun (n, rs) ->
          if List.mem 2 rs then part1 := !part1 + n;
          if not (rs = [ 1 ]) then part2 := !part2 + n));
  Flow.copy_string (sprintf "Part1: %d\n" !part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" !part2) stdout
