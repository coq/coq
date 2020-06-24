#!/usr/bin/env ocaml

let get_pkg_name arg =
  List.nth (String.split_on_char ':' arg) 0

let get_pkg_deps arg =
  String.split_on_char ',' (List.nth (String.split_on_char ':' arg) 1)

let split_pkg arg = get_pkg_name arg, get_pkg_deps arg

let depends_on arg1 arg2 =
  let pkg1, deps1 = split_pkg arg1 in
  let pkg2, deps2 = split_pkg arg2 in
  pkg1 != pkg2 && List.mem pkg2 deps1

let rec sort = function
  | [], [] -> []
  | [], deferred -> sort (List.rev deferred, [])
  | arg :: rest, deferred ->
    (* check if any remaining package reverse-depends on this one *)
    if List.exists (fun other_arg -> depends_on arg other_arg) rest
    then (* defer this package *)
      sort (rest, arg :: deferred)
    else (* emit this package, and then try again with any deferred packages *)
      arg :: sort (List.rev deferred @ rest, [])

let main () =
  let args = Array.to_list Sys.argv in
  let pkgs = List.tl args in
  let sorted_pkgs = sort (pkgs, []) in
  Printf.printf "%s\n%!" (String.concat " " (List.map get_pkg_name sorted_pkgs))

let () = main ()
