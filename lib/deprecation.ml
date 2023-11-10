(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = { since : string option ; note : string option }

let make ?since ?note () = { since ; note }

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

let printer ~object_name pp (x,{since;note}) =
  let open Pp in
  str object_name ++ spc () ++ pp x ++
  strbrk " is deprecated" ++
  pr_opt (fun since -> str "since " ++ str since) since ++
  str "." ++ pr_opt (fun note -> str note) note

let create_warning ~object_name ~warning_name_if_no_since pp =
  let pp = printer ~object_name pp in
  let main_cat, main_w = CWarnings.create_hybrid ~name:warning_name_if_no_since ~from:[depr_cat] () in
  let main_w = CWarnings.create_in main_w pp in
  let warnings = ref CString.Map.empty in
  fun ?loc (v, ({since} as info)) ->
    let since = since_name since in
    let w = match since with
      | NoSince -> main_w
      | Since since ->
        match CString.Map.find_opt since !warnings with
        | Some w -> w
        | None ->
          let generic_cat = get_generic_cat since in
          let w = CWarnings.create_warning ~from:[main_cat; generic_cat]
              ~name:(warning_name_if_no_since ^ "-since-" ^ since) ()
          in
          let w = CWarnings.create_in w pp in
          warnings := CString.Map.add since w !warnings;
          w
    in
    w ?loc (v,info)

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

end
