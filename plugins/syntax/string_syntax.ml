(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Globnames
open Ascii_syntax_plugin.Ascii_syntax
open Glob_term
open Coqlib

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "string_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

exception Non_closed_string

(* make a string term from the string s *)

let string_module = ["Coq";"Strings";"String"]

let string_path = make_path string_module "string"

let string_kn = make_kn string_module "string"
let static_glob_EmptyString  = ConstructRef ((string_kn,0),1)
let static_glob_String  = ConstructRef ((string_kn,0),2)

let make_reference id = find_reference "String interpretation" string_module id
let glob_String = lazy (make_reference "String")
let glob_EmptyString = lazy (make_reference "EmptyString")

let is_gr c gr = match DAst.get c with
| GRef (r, _) -> GlobRef.equal r gr
| _ -> false

open Lazy

let interp_string ?loc s =
  let le = String.length s in
  let rec aux n =
     if n = le then DAst.make ?loc @@ GRef (force glob_EmptyString, None) else
     DAst.make ?loc @@ GApp (DAst.make ?loc @@ GRef (force glob_String, None),
       [interp_ascii ?loc (int_of_char s.[n]); aux (n+1)])
  in aux 0

let uninterp_string (AnyGlobConstr r) =
  try
    let b = Buffer.create 16 in
    let rec aux c = match DAst.get c with
    | GApp (k,[a;s]) when is_gr k (force glob_String) ->
	(match uninterp_ascii a with
	  | Some c -> Buffer.add_char b (Char.chr c); aux s
	  | _ -> raise Non_closed_string)
    | GRef (z,_) when GlobRef.equal z (force glob_EmptyString) ->
	Some (Buffer.contents b)
    | _ ->
	raise Non_closed_string
    in aux r
  with
   Non_closed_string -> None

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let _ =
  let sc = "string_scope" in
  register_string_interpretation sc (interp_string,uninterp_string);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = sc;
      pt_interp_info = Uid sc;
      pt_required = (string_path,["Coq";"Strings";"String"]);
      pt_refs = [static_glob_String; static_glob_EmptyString];
      pt_in_match = true }
