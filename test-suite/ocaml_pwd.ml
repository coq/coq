let _ =
  let ch_dir = Sys.argv.(1) in
  Sys.chdir ch_dir;
  let dir = Sys.getcwd () in
  (* Needed for windows *)
  let dir = Filename.quote dir in
  Format.printf "%s%!" dir
