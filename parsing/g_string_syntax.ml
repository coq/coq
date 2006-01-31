(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

open Pp
open Util
open Names
open Pcoq
open Libnames
open Topconstr
open G_ascii_syntax
open Rawterm

exception Non_closed_string

(* make a string term from the string s *)

let string_module = make_dir ["Coq";"Strings";"String"]
let string_path = make_path string_module (id_of_string "string")

let glob_string  = IndRef (string_path,0)
let path_of_EmptyString  = ((string_path,0),1)
let glob_EmptyString  = ConstructRef path_of_EmptyString
let path_of_String  = ((string_path,0),2)
let glob_String  = ConstructRef path_of_String

let interp_string dloc s =
  let le = String.length s in
  let rec aux n = 
     if n = le then RRef (dloc, glob_EmptyString) else
     RApp (dloc,RRef (dloc, glob_String),
       [interp_ascii dloc (int_of_char s.[n]); aux (n+1)])
  in aux 0

let uninterp_string r =
  try 
    let b = Buffer.create 16 in
    let rec aux = function
    | RApp (_,RRef (_,k),[a;s]) when k = glob_String ->
	(match uninterp_ascii a with
	  | Some c -> Buffer.add_char b (Char.chr c); aux s
	  | _ -> raise Non_closed_string)
    | RRef (_,z) when z = glob_EmptyString ->
	Some (Buffer.contents b)
    | _ ->
	raise Non_closed_string
    in aux r
  with 
   Non_closed_string -> None

let _ =
  Notation.declare_string_interpreter "string_scope"
    (glob_string,["Coq";"Strings";"String"])
    interp_string
    ([RRef (dummy_loc,glob_String); RRef (dummy_loc,glob_EmptyString)],
     uninterp_string, true)
