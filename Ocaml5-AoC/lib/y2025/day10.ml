open Angstrom
open Aoc
open Eio
open Format

let parse_indicator =
  char '['
  *> ( take_while1 (function '.' | '#' -> true | _ -> false) >>| fun s ->
       String.to_seq s |> Seq.map (fun ch -> ch = '#') |> Array.of_seq )
  <* string "] "

let parse_button = char '(' *> Parsers.separated Parsers.integer (char ',') <* string ") "
let parse_buttons = many1 parse_button
let parse_goal = char '{' *> Parsers.separated Parsers.integer (char ',') <* char '}'
let parse_line = lift3 (fun a b c -> (a, b, c)) parse_indicator parse_buttons parse_goal
let parser = Parsers.separated parse_line end_of_line <* end_of_line <* end_of_input

module Map = Hashtbl.Make (struct
  type t = bool array

  let equal v1 v2 = v1 = v2
  (* Array.length v1 = Array.length v2 && Array.to_seqi v1 |> Seq.for_all (fun (i, b) -> b = v2.(i)) *)

  let hash = Hashtbl.hash
end)

let solve1 (indicator : bool array) (buttons : int array list) : int =
  let checked = Map.create 64
  and to_visit = ref @@ Map.create 64
  and next = Map.create 64
  and steps = ref 0
  and continue = ref true in
  Map.add !to_visit Array.(make (length indicator) false) ();
  while !continue do
    Map.clear next;
    let cands = Map.to_seq_keys !to_visit |> Array.of_seq in
    for i = 0 to Array.length cands - 1 do
      if !continue then begin
        let state = cands.(i) in
        if state = indicator then continue := false
        else if not (Map.mem checked state) then begin
          Map.add checked state ();
          List.to_seq buttons
          |> Seq.iter (fun btn_spec ->
              let s = Array.copy state in
              Array.to_seq btn_spec |> Seq.iter (fun i -> s.(i) <- not s.(i));
              Map.replace next s ();
              ())
        end
      end
    done;
    if !continue then begin
      to_visit := Map.copy next;
      assert (0 < Map.length !to_visit);
      steps := !steps + 1
    end
  done;
  !steps

let solve data_file stdout =
  let data =
    match Angstrom.(parse_string ~consume:Prefix parser @@ Path.load data_file) with
    | Ok v -> v
    | Error msg -> failwith msg
  in
  (* print_endline @@ [%show: (bool array * int array list * int array) array] data; *)
  let part1 = Array.to_seq data |> Seq.map (fun (i, b, _) -> solve1 i b) |> Seq.fold_left ( + ) 0
  and part2 = 0 in
  Flow.copy_string (sprintf "Part1: %d\n" part1) stdout;
  Flow.copy_string (sprintf "Part2: %d\n" part2) stdout
