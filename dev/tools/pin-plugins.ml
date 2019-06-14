(** Pin third-party developments in CI scipt.

Usage: ocaml unix.cma str.cma pin-plugins.ml | sh

This program scans the file containing the references to third-party
developments used in CI and looks for definitions like “mathcomp_CI_REF:=master”
and “mathcomp_CI_GITURL:=https://github.com/math-comp/math-comp”. It then
generates a shell script that calls sed in order to replace in the *_CI_REF
definitions the branch name by a commit identifier; such identifier is obtained
by calling “git ls-remote” on the corresponding URL.

*)

(** Fold function [f] on all lines from input [ic] with initial value [z] *)
let fold_lines ic f z =
  let rec loop acc =
    match input_line ic with
    | exception End_of_file -> acc
    | line -> f acc line |> loop
  in loop z

let path = "../ci/ci-basic-overlay.sh"

let re = Str.regexp ".*\\${\\([a-zA-Z_]+\\)_CI_\\(REF\\|GITURL\\):=\\([^}]+\\)}.*"
let git_ls = Str.regexp "\\([0-9a-f]+\\)\trefs/\\([^/]+\\)/\\(.*\\)$"

let () =
  let refs = Hashtbl.create 17 in
  let urls = Hashtbl.create 17 in
  let ic = open_in path in
  fold_lines ic
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
  close_in ic;
  Format.printf "sed -i \\@.";
  Hashtbl.iter
    (fun name url ->
      match Hashtbl.find refs name with
      | exception Not_found -> Format.eprintf "Warning: ignoring %s.@." name
      | ref ->
        let tags = Hashtbl.create 17 in
        let cmd = Format.sprintf "git ls-remote --head --tag %s" url in
        let ic = Unix.open_process_in cmd in
        let new_refs =
          fold_lines ic
            (fun acc line ->
               if Str.string_match git_ls line 0
               then
                 let hash = Str.matched_group 1 line in
                 let tag = Str.matched_group 3 line in
                 match Str.matched_group 2 line with
                 | "tags" -> Hashtbl.add tags hash tag; acc
                 | "heads" -> if tag = ref then hash :: acc else acc
                 | _ -> acc
               else acc
            )
            []
        in
        ic |> Unix.close_process_in |> (ignore : Unix.process_status -> unit);
        match new_refs with
        | [] -> Format.eprintf "Warning: no head matching %s at %s.@." name url
        | r :: extra ->
          begin
            if extra <> [] then Format.eprintf "Warning: more than one head matching %s at %s.@." name url;
            let new_ref = try Hashtbl.find tags r with Not_found -> r in
            Format.printf "-e \"s/%s_CI_REF:=%s/%s_CI_REF:=%s/\" \\@." name ref name new_ref
          end
    )
    urls;
  Format.printf "%s@." path
