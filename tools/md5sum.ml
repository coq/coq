let () =
  match Sys.argv with
  | [|_; file|] ->
      let md5 = Digest.to_hex (Digest.file file) in
      print_endline (md5 ^ "  " ^ file)
  | _ ->
      prerr_endline "Error: This program needs exactly one parameter.";
      prerr_endline "Usage: ocaml md5sum.ml [FILE]";
      prerr_endline "Print MD5 (128-bit) checksum.";
      exit 1
