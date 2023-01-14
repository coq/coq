let back_to_root dir =
  let rec back_to_root_aux = function
  | [] -> []
  | l :: ls -> ".." :: back_to_root_aux ls
  in
  Str.split (Str.regexp "/") dir
  |> back_to_root_aux
  |> String.concat "/"

let scan_files_by_ext ~ext ?(ignore=[]) dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ext)
  |> List.filter (fun f -> not @@ List.mem f ignore)

let scan_dirs ?(ignore=[]) dir =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun subdir -> Sys.is_directory (Filename.concat dir subdir))
  |> List.filter (fun subdir -> not @@ List.mem subdir ignore)
