let _ =
  let quoted = Sys.argv.(1) = "-quoted" in
  let ch_dir = Sys.argv.(if quoted then 2 else 1) in
  Sys.chdir ch_dir;
  let dir = Sys.getcwd () in
  let dir = if quoted then Filename.quote dir else dir in
  Format.printf "%s%!" dir
