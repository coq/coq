let get_content file =
  let ic = open_in_bin file in
  let buf = Buffer.create 2048 in
  let rec fill () =
    match input_char ic with
    | '\r' -> fill () (* NOTE: handles the case on Windows where the
                         git checkout has included return characters.
                         See: https://github.com/coq/coq/pull/6305 *)
    | c -> Buffer.add_char buf c; fill ()
    | exception End_of_file -> close_in ic; Buffer.contents buf
  in
  fill ()

let () =
  match Sys.argv with
  | [|_; file|] ->
      let content = get_content file in
      let md5 = Digest.to_hex (Digest.string content) in
      print_string (md5 ^ " " ^ file)
  | _ ->
      prerr_endline "Error: This program needs exactly one parameter.";
      prerr_endline "Usage: ocaml md5sum.ml <FILE>";
      prerr_endline "Print MD5 (128-bit) checksum of the file content modulo \\r.";
      exit 1
