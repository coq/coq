(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Pcoq
open Rawterm
open Topconstr
open Libnames
open Coqlib
open Bigint

exception Non_closed_ascii

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let make_kn dir id = Libnames.encode_kn (make_dir dir) (id_of_string id)
let make_path dir id = Libnames.make_path (make_dir dir) (id_of_string id)

let ascii_module = ["Coq";"Strings";"Ascii"]

let ascii_path = make_path ascii_module "ascii"

let ascii_kn = make_kn ascii_module "ascii"
let path_of_Ascii = ((ascii_kn,0),1)
let static_glob_Ascii  = ConstructRef path_of_Ascii

let make_reference id = find_reference "Ascii interpretation" ascii_module id
let glob_Ascii = lazy (make_reference "Ascii")

open Lazy

let interp_ascii dloc p =
  let rec aux n p = 
     if n = 0 then [] else
     let mp = p mod 2 in
     RRef (dloc,if mp = 0 then glob_false else glob_true)
     :: (aux (n-1) (p/2)) in
  RApp (dloc,RRef(dloc,force glob_Ascii), aux 8 p)

let interp_ascii_string dloc s =
  let p = 
    if String.length s = 1 then int_of_char s.[0]
    else
      if String.length s = 3 & is_digit s.[0] & is_digit s.[1] & is_digit s.[2]
      then int_of_string s
      else
	user_err_loc (dloc,"interp_ascii_string",
	  str "Expects a single character or a three-digits ascii code.") in
  interp_ascii dloc p

let uninterp_ascii r =
  let rec uninterp_bool_list n = function
    | [] when n = 0 -> 0
    | RRef (_,k)::l when k = glob_true  -> 1+2*(uninterp_bool_list (n-1)  l)
    | RRef (_,k)::l when k = glob_false -> 2*(uninterp_bool_list (n-1) l)
    | _ -> raise Non_closed_ascii in
  try 
    let rec aux = function
    | RApp (_,RRef (_,k),l) when k = force glob_Ascii -> uninterp_bool_list 8 l
    | _ -> raise Non_closed_ascii in
    Some (aux r)
  with 
   Non_closed_ascii -> None

let make_ascii_string n =
  if n>=32 && n<=126 then String.make 1 (char_of_int n)
  else Printf.sprintf "%03d" n

let uninterp_ascii_string r = Option.map make_ascii_string (uninterp_ascii r)

let _ =
  Notation.declare_string_interpreter "char_scope"
    (ascii_path,ascii_module)
    interp_ascii_string
    ([RRef (dummy_loc,static_glob_Ascii)], uninterp_ascii_string, true)
