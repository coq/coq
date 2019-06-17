(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


let all_bindings = ref []
  (* example unicode bindings table:
  [ ("\\pi", "π", None);
    ("\\lambdas", "λs", Some 4);
    ("\\lambda", "λ", Some 3);
    ("\\lake", "0", Some 2);
    ("\\lemma", "Lemma foo : x. Proof. Qed", Some 1); ] *)

(** Auxiliary function used by [load_files].
    Takes as argument a valid path. *)

let process_file filename =
  if not (Sys.file_exists filename) then begin
    Ideutils.warning (Printf.sprintf "Warning: unicode bindings file '%s' was not found." filename)
  end else begin
    let ch = open_in filename in
    begin try while true do
      let line = input_line ch in
      begin try
        let chline = Scanf.Scanning.from_string line in
        let (key,value) =
          Scanf.bscanf chline "%s %s" (fun x y -> (x,y)) in
        let prio =
          try Scanf.bscanf chline " %d" (fun x -> Some x)
          with Scanf.Scan_failure _ | Failure _ | End_of_file -> None
          in
        all_bindings := (key,value,prio)::!all_bindings;
        (* Note: storing bindings in reverse order, flipping is done later *)
        Scanf.Scanning.close_in chline;
      with End_of_file -> () end;
    done with End_of_file -> () end;
    close_in ch
  end

let load_files filenames =
  let selected_filenames = ref [] in
  let add f =
    selected_filenames := f::!selected_filenames in
  let warn_default_not_found () =
    Ideutils.warning (Printf.sprintf
      "Warning: the file 'ide/default.bindings' was not found in %s."
      (Envars.coqlib())) in
  let warn_local_not_found () =
    Ideutils.warning (Printf.sprintf
      "Warning: the local configuration file 'coqide.bindings' was not found.") in
  if filenames = [] then begin
    (* If no argument is provided using [-unicode-bindings],
       then use the default file and the local file, if it exists *)
    begin match Preferences.get_unicode_bindings_default_file() with
    | Some f -> add f
    | None -> warn_default_not_found()
    end;
    begin match Preferences.get_unicode_bindings_local_file() with
    | Some f -> add f
    | None -> ()
    end;
  end else begin
    (* If [-unicode-bindings] is used with a list of file, consider
       these files in order, with a special treatment for the tokens
       "default" and "local", which are replaced by the appropriate path. *)
    let add_arg f =
      match f with
      | "default" ->
        begin match Preferences.get_unicode_bindings_default_file() with
        | Some f -> add f
        | None -> warn_default_not_found()
        end
      | "local" ->
        begin match Preferences.get_unicode_bindings_local_file() with
        | Some f -> add f
        | None -> warn_local_not_found()
        end
      | _ -> add f
      in
    List.iter add_arg filenames
  end;
  (* Files must be processed in order, to build the list of bindings
     by iteratively consing entry to its head, the list being reversed
     at the very end *)
  let real_filenames = List.rev !selected_filenames in
  List.iter process_file real_filenames;
  all_bindings := List.rev !all_bindings
  (* For debugging the list of unicode files loaded:
     List.iter (fun f -> Printf.eprintf "%s\n" f) real_filenames; *)

(** Auxiliary function to test whether [s] is a prefix of [str];
    Note that there might be overlap with wg_Completion::is_substring *)

let string_is_prefix s str =
  let n = String.length s in
  let m = String.length str in
  if m < n
    then false
    else (s = String.sub str 0 n)

let lookup prefix =
  let max_priority = 100000000 in
  let cur_word = ref None in
  let cur_prio = ref (max_priority+1) in
  let test_binding (key, word, prio_opt) =
    let prio =
      match prio_opt with
      | None -> max_priority
      | Some p -> p
      in
    if string_is_prefix prefix key && prio < !cur_prio then begin
      cur_word := Some word;
      cur_prio := prio;
    end in
  List.iter test_binding !all_bindings;
  !cur_word


(* For debugging the list of unicode bindings loaded:
  let print_unicode_bindings () =
    List.iter (fun (x,y,p) ->
      Printf.eprintf "%s %s %d\n" x y (match p with None -> -1 | Some n -> n))
     !all_bindings;
    prerr_newline()
*)
