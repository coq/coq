(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "ascii_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

open Pp
open CErrors
open Util
open Names
open Glob_term
open Globnames
open Coqlib

exception Non_closed_ascii

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_kn dir id = Globnames.encode_mind (make_dir dir) (Id.of_string id)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let is_gr c gr = match DAst.get c with
| GRef (r, _) -> GlobRef.equal r gr
| _ -> false

let ascii_module = ["Coq";"Strings";"Ascii"]

let ascii_path = make_path ascii_module "ascii"

let ascii_kn = make_kn ascii_module "ascii"
let path_of_Ascii = ((ascii_kn,0),1)
let static_glob_Ascii  = ConstructRef path_of_Ascii

let make_reference id = find_reference "Ascii interpretation" ascii_module id
let glob_Ascii = lazy (make_reference "Ascii")

open Lazy

let interp_ascii ?loc p =
  let rec aux n p =
     if Int.equal n 0 then [] else
     let mp = p mod 2 in
     (DAst.make ?loc @@ GRef ((if Int.equal mp 0 then glob_false else glob_true),None))
     :: (aux (n-1) (p/2)) in
  DAst.make ?loc @@ GApp (DAst.make ?loc @@ GRef(force glob_Ascii,None), aux 8 p)

let interp_ascii_string ?loc s =
  let p =
    if Int.equal (String.length s) 1 then int_of_char s.[0]
    else
      if Int.equal (String.length s) 3 && is_digit s.[0] && is_digit s.[1] && is_digit s.[2]
      then int_of_string s
      else
	user_err ?loc ~hdr:"interp_ascii_string"
	 (str "Expects a single character or a three-digits ascii code.") in
  interp_ascii ?loc p

let uninterp_ascii r =
  let rec uninterp_bool_list n = function
    | [] when Int.equal n 0 -> 0
    | r::l when is_gr r glob_true  -> 1+2*(uninterp_bool_list (n-1)  l)
    | r::l when is_gr r glob_false -> 2*(uninterp_bool_list (n-1) l)
    | _ -> raise Non_closed_ascii in
  try
    let aux c = match DAst.get c with
    | GApp (r, l) when is_gr r (force glob_Ascii) -> uninterp_bool_list 8 l
    | _ -> raise Non_closed_ascii in
    Some (aux r)
  with
   Non_closed_ascii -> None

let make_ascii_string n =
  if n>=32 && n<=126 then String.make 1 (char_of_int n)
  else Printf.sprintf "%03d" n

let uninterp_ascii_string (AnyGlobConstr r) = Option.map make_ascii_string (uninterp_ascii r)

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let _ =
  let sc = "char_scope" in
  register_string_interpretation sc (interp_ascii_string,uninterp_ascii_string);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = sc;
      pt_interp_info = Uid sc;
      pt_required = (ascii_path,ascii_module);
      pt_refs = [static_glob_Ascii];
      pt_in_match = true }
