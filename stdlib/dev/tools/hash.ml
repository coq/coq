let () =
  Printf.printf "%s\n%!" Digest.(to_hex (input stdin))
