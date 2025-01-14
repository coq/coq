let pp_arch arch ch =
  Printf.fprintf ch "%s" arch

let idearchdef ocamlfind arch =
  match arch with
    | "Darwin" ->
      let osxdir,_ = Conf.Util.tryrun ocamlfind ["query";"lablgtkosx"] in
      if osxdir <> "" then "QUARTZ" else "X11"
    | "win32" ->
      "WIN32"
    | _ -> "X11"

let write_configide idearchdef o =
  let pr s = Printf.fprintf o s in
  pr "let gtk_platform = `%s\n" idearchdef

let main () =
  let arch = Conf.Util.arch None in
  let idearch = idearchdef "ocamlfind" arch in
  Conf.Util.write_config_file ~file:"gtk_platform.conf" (pp_arch idearch);
  Conf.Util.write_config_file ~file:"config.ml" (write_configide idearch);
  ()

let () = main ()
