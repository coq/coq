(** Pin third-party developments in CI scipt.

Usage: ocaml str.cma pin-plugins.ml | sh

This program scans the file containing the references to third-party
developments used in CI and looks for definitions like “mathcomp_CI_REF:=master”
and “mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp”. It then
generates a shell script that calls sed in order to replace in the *_CI_REF
definitions the branch name by a commit identifier; such identifier is optained
by calling “git ls-remote” on the corresponding URL.

*)

(** Fold function [f] on all lines of file at [path] with initial value [z] *)
let read_file path f z =
  let ic = open_in path in
  let rec loop acc =
    match input_line ic with
    | exception End_of_file -> close_in ic; acc
    | line -> f acc line |> loop
  in loop z

let path = "../ci/ci-basic-overlay.sh"

let re = Str.regexp ".*\\${\\([a-zA-Z_]+\\)_CI_\\(REF\\|GITURL\\):=\\([^}]+\\)}.*"

let () =
  let refs = Hashtbl.create 17 in
  let urls = Hashtbl.create 17 in
  read_file path
  (fun acc line ->
    if Str.string_match re line 0
    then (
      let key = Str.matched_group 1 line in
      let value = Str.matched_group 3 line in
      match Str.matched_group 2 line with
      | "REF" -> Hashtbl.add refs key value
      | "GITURL" -> Hashtbl.add urls key value
      | _ -> acc
    )
    else acc
  ) ();
  Format.printf "sed -i \\@.";
  Hashtbl.iter
    (fun name url ->
      match Hashtbl.find refs name with
      | exception Not_found -> Format.eprintf "Warning: ignoring %s.@." name
      | ref ->
          Format.printf "-e \"s/%s_CI_REF:=%s/%s_CI_REF:=$(git ls-remote %s %s | head -1 | awk '{print $1}')/\" \\@." name ref name url ref
    )
  urls;
  Format.printf "%s@." path
