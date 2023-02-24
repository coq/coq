let plugins =
  try Sys.readdir "plugins"
  with _ -> [||]

let () = Array.sort compare plugins

let () = Array.iter (fun f ->
    let f' = "plugins/"^f in
    if Sys.is_directory f' && f.[0] <> '.' then print_endline f)
    plugins
