(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = { since : string option ; note : string option }
type 'a with_qf = { depr : t; use_instead : 'a option }

let drop_qf { depr } = depr
let with_empty_qf depr = { depr; use_instead = None }

let make ?since ?note () = { since ; note }
let make_with_qf ?since ?note ?use_instead () = { depr = make ?since ?note (); use_instead }

type since_name = NoSince | Since of string

let since_name = function
  | None -> NoSince
  | Some s -> Since (String.map (function ' ' -> '-' | c -> c) s)

let depr_cat = CWarnings.CoreCategories.deprecated

let since_cats = ref CString.Map.empty

let get_generic_cat since =
  match CString.Map.find_opt since !since_cats with
  | Some c -> c
  | None ->
    let c = CWarnings.create_category ~from:[depr_cat] ~name:("deprecated-since-"^since) () in
    since_cats := CString.Map.add since c !since_cats;
    c

let printer ~object_name ~pp_qf pp (x,{depr={since;note};use_instead}) =
  let open Pp in
  let note =
    match note, use_instead with
    | None, None -> None
    | Some x, _ -> Some (str x)
    | None, Some x -> Some (str"Use " ++ pp_qf x ++ str" instead.") in
  str object_name ++ spc () ++ pp x ++
  strbrk " is deprecated" ++
  pr_opt (fun since -> str "since " ++ str since) since ++
  str "." ++ pr_opt (fun x -> x) note

let create_warning_with_qf ?default ~object_name ~warning_name_if_no_since ~pp_qf pp =
  let pp = printer ~object_name ~pp_qf pp in
  let main_cat, main_w = CWarnings.create_hybrid ?default ~name:warning_name_if_no_since ~from:[depr_cat] () in
  let main_w = CWarnings.create_in main_w pp in
  let warnings = ref CString.Map.empty in
  fun ?loc (v, ({depr = {since}; use_instead } as info)) ->
    let since = since_name since in
    let quickfix =
      match use_instead with
      | None -> None
      | Some replacement ->
          Option.cata (fun loc -> Some [Quickfix.make ~loc (pp_qf replacement)]) None loc in
    let w = match since with
      | NoSince -> main_w
      | Since since ->
        match CString.Map.find_opt since !warnings with
        | Some w -> w
        | None ->
          let generic_cat = get_generic_cat since in
          let w = CWarnings.create_warning ?default ~from:[main_cat; generic_cat]
              ~name:(warning_name_if_no_since ^ "-since-" ^ since) ()
          in
          let w = CWarnings.create_in w pp in
          warnings := CString.Map.add since w !warnings;
          w
    in
    w ?loc ?quickfix (v,info)

let create_warning ?default ~object_name ~warning_name_if_no_since pp =
  let f = create_warning_with_qf ?default ~object_name ~warning_name_if_no_since ~pp_qf:(fun _ -> assert false) pp in
  fun ?loc (v, depr) -> f ?loc (v, {depr; use_instead = None})

module Version = struct

  let v8_3 = get_generic_cat "8.3"
  let v8_5 = get_generic_cat "8.5"
  let v8_8 = get_generic_cat "8.8"
  let v8_10 = get_generic_cat "8.10"
  let v8_11 = get_generic_cat "8.11"
  let v8_14 = get_generic_cat "8.14"
  let v8_15 = get_generic_cat "8.15"
  let v8_16 = get_generic_cat "8.16"
  let v8_17 = get_generic_cat "8.17"
  let v8_18 = get_generic_cat "8.18"
  let v8_19 = get_generic_cat "8.19"
  let v8_20 = get_generic_cat "8.20"
  let v9_0 = get_generic_cat "9.0"
  let v9_1 = get_generic_cat "9.1"
  (* When adding a new version here, please also add
     #[export] Set Warnings "-deprecated-since-X.Y".
     in theories/Compat/RocqX{Y-1}.v *)

end
