let () =
  for _ = 1 to 4 do
    print_endline "Hello, World!";
    print_endline ("AOC_DIR: " ^ (Sys.getenv_opt "AOC_DIR" |> Option.value ~default:""))
  done
