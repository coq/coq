(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Globnames
open Ascii_syntax
open Glob_term
open Coqlib

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

open Lazy

let interp_string dloc s =
  let le = String.length s in
  let rec aux n =
     if n = le then GRef (dloc, force glob_EmptyString, None) else
     GApp (dloc,GRef (dloc, force glob_String, None),
       [interp_ascii dloc (int_of_char s.[n]); aux (n+1)])
  in aux 0

let uninterp_string r =
  try
    let b = Buffer.create 16 in
    let rec aux = function
    | GApp (_,GRef (_,k,_),[a;s]) when eq_gr k (force glob_String) ->
	(match uninterp_ascii a with
	  | Some c -> Buffer.add_char b (Char.chr c); aux s
	  | _ -> raise Non_closed_string)
    | GRef (_,z,_) when eq_gr z (force glob_EmptyString) ->
	Some (Buffer.contents b)
    | _ ->
	raise Non_closed_string
    in aux r
  with
   Non_closed_string -> None

let _ =
  Notation.declare_string_interpreter "string_scope"
    (string_path,["Coq";"Strings";"String"])
    interp_string
    ([GRef (Loc.ghost,static_glob_String,None);
      GRef (Loc.ghost,static_glob_EmptyString,None)],
     uninterp_string, true)
