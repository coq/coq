(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This is about warnings triggered from user .v code ("warn" attibute).
    See cWarnings.mli for the generic warning interface. *)

type warn = { note : string; cats : string }
(** note and comma separated list of categories *)

type t = { depr : Deprecation.t option; warn : warn list }
type 'a with_qf = { depr_qf : 'a Deprecation.with_qf option; warn_qf : warn list }

let drop_qf { depr_qf; warn_qf } = { depr = Option.map Deprecation.drop_qf depr_qf; warn = warn_qf }
let with_empty_qf { depr; warn } = { depr_qf = Option.map Deprecation.with_empty_qf depr; warn_qf = warn}
let empty = { depr = None; warn = [] }

let make_warn ~note ?cats () =
  let l = String.split_on_char ',' (Option.default "" cats) in
  let l =
    List.map String.(fun s -> map (function ' ' -> '-' | c -> c) (trim s)) l in
  let l = List.sort String.compare l in
  { note; cats = String.concat "," l }

let user_warn_cat = CWarnings.CoreCategories.user_warn

let warn_cats = ref CString.Map.empty

let get_generic_cat cat =
  match CString.Map.find_opt cat !warn_cats with
  | Some c -> c
  | None ->
    let c = CWarnings.create_category ~from:[user_warn_cat] ~name:cat () in
    warn_cats := CString.Map.add cat c !warn_cats;
    c

let create_warning ?default ~warning_name_if_no_cats () =
  let main_cat, main_w = CWarnings.create_hybrid ?default ~name:warning_name_if_no_cats ~from:[user_warn_cat] () in
  let main_w = CWarnings.create_in main_w Pp.strbrk in
  let warnings = ref CString.Map.empty in
  fun ?loc {note;cats} ->
    let w =
      if cats = "" then main_w else
        match CString.Map.find_opt cats !warnings with
        | Some w -> w
        | None ->
           let l = String.split_on_char ',' cats in
           let generic_cats = List.map get_generic_cat l in
           let w = CWarnings.create_warning ?default ~from:(main_cat :: generic_cats)
               ~name:(String.concat "-" (warning_name_if_no_cats :: l)) () in
           let w = CWarnings.create_in w Pp.strbrk in
           warnings := CString.Map.add cats w !warnings;
           w
    in
    w ?loc note

let create_depr_and_user_warnings ?default ~object_name ~warning_name_base pp () =
  let depr_warning = Deprecation.create_warning ?default
      ~object_name ~warning_name_if_no_since:("deprecated-"^warning_name_base) pp
  in
  let user_warning = create_warning ?default
      ~warning_name_if_no_cats:("warn-"^warning_name_base) ()
  in
  fun ?loc x w ->
    w.depr |> Option.iter (fun depr -> depr_warning ?loc (x,depr));
    w.warn |> List.iter (fun w -> user_warning ?loc w)
