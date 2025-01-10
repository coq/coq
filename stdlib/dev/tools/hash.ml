let () =
  Printf.printf "%s\n%!" Digest.(to_hex (file Sys.argv.(1)))
