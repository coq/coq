(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Coqast
open Pcoq
open Pp
open Util
open Names
open Ast
open Extend
open Topconstr
open Libnames
open Bignat

(**********************************************************************)
(* Parsing positive via scopes                                        *)
(**********************************************************************)

open Libnames
open Rawterm
let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let fast_integer_module = make_dir ["Coq";"ZArith";"fast_integer"]

(* TODO: temporary hack *)
let make_path dir id = Libnames.encode_kn dir id

let positive_path = make_path fast_integer_module (id_of_string "positive")
let path_of_xI = ((positive_path,0),1)
let path_of_xO = ((positive_path,0),2)
let path_of_xH = ((positive_path,0),3)
let glob_xI = ConstructRef path_of_xI
let glob_xO = ConstructRef path_of_xO
let glob_xH = ConstructRef path_of_xH

let pos_of_bignat dloc x =
  let ref_xI = RRef (dloc, glob_xI) in
  let ref_xH = RRef (dloc, glob_xH) in
  let ref_xO = RRef (dloc, glob_xO) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> RApp (dloc, ref_xO,[pos_of q])
      | (q,true) when is_nonzero q -> RApp (dloc,ref_xI,[pos_of q])
      | (q,true) -> ref_xH
  in 
  pos_of x

let interp_positive dloc = function
  | POS n when is_nonzero n -> pos_of_bignat dloc n
  | _ ->
      user_err_loc (dloc, "interp_positive",
        str "Only strictly positive numbers in type \"positive\"!")

let rec pat_pos_of_bignat dloc x name =
  match div2_with_rest x with
    | (q,false) -> 
        PatCstr (dloc,path_of_xO,[pat_pos_of_bignat dloc q Anonymous],name)
    | (q,true) when is_nonzero q -> 
        PatCstr (dloc,path_of_xI,[pat_pos_of_bignat dloc q Anonymous],name)
    | (q,true) ->
        PatCstr (dloc,path_of_xH,[],name)

let pat_interp_positive dloc = function
  | POS n -> pat_pos_of_bignat dloc n
  | NEG n ->
      user_err_loc (dloc, "interp_positive",
        str "No negative number in type \"positive\"!")

(**********************************************************************)
(* Printing positive via scopes                                       *)
(**********************************************************************)

exception Non_closed_number

let rec bignat_of_pos = function
  | RApp (_, RRef (_,b),[a]) when b = glob_xO -> mult_2(bignat_of_pos a)
  | RApp (_, RRef (_,b),[a]) when b = glob_xI -> add_1(mult_2(bignat_of_pos a))
  | RRef (_, a) when a = glob_xH -> Bignat.one
  | _ -> raise Non_closed_number

let uninterp_positive p =
  try 
    Some (POS (bignat_of_pos p))
  with Non_closed_number -> 
    None

(***********************************************************************)
(* Declaring interpreters and uninterpreters for positive *)
(***********************************************************************)

let _ = Symbols.declare_numeral_interpreter "positive_scope"
  ["Coq";"ZArith";"fast_integer"]
  (interp_positive,Some pat_interp_positive)
  ([RRef (dummy_loc, glob_xI); 
    RRef (dummy_loc, glob_xO); 
    RRef (dummy_loc, glob_xH)],
   uninterp_positive,
   None)

(**********************************************************************)
(* Parsing Z via scopes                                               *)
(**********************************************************************)

let z_path = make_path fast_integer_module (id_of_string "Z")
let glob_z = IndRef (z_path,0)
let path_of_ZERO = ((z_path,0),1)
let path_of_POS = ((z_path,0),2)
let path_of_NEG = ((z_path,0),3)
let glob_ZERO = ConstructRef path_of_ZERO
let glob_POS = ConstructRef path_of_POS
let glob_NEG = ConstructRef path_of_NEG

let z_of_posint dloc pos_or_neg n = 
  if is_nonzero n then
    let sgn = if pos_or_neg then glob_POS else glob_NEG in
    RApp(dloc, RRef (dloc,sgn), [pos_of_bignat dloc n])
  else 
    RRef (dloc, glob_ZERO)

let z_of_int dloc z =
  match z with
  | POS n -> z_of_posint dloc true n 
  | NEG n -> z_of_posint dloc false n 

let pat_z_of_posint dloc pos_or_neg n name = 
  if is_nonzero n then
    let sgn = if pos_or_neg then path_of_POS else path_of_NEG in
    PatCstr (dloc, sgn, [pat_pos_of_bignat dloc n Anonymous], name)
  else 
    PatCstr (dloc, path_of_ZERO, [], name)

let pat_z_of_int dloc n name =
  match n with
  | POS n -> pat_z_of_posint dloc true n name
  | NEG n -> pat_z_of_posint dloc false n name

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z = function
  | RApp (_, RRef (_,b),[a]) when b = glob_POS -> POS (bignat_of_pos a)
  | RApp (_, RRef (_,b),[a]) when b = glob_NEG -> NEG (bignat_of_pos a)
  | RRef (_, a) when a = glob_ZERO -> POS (Bignat.zero)
  | _ -> raise Non_closed_number

let uninterp_z p =
  try
    Some (bigint_of_z p)
  with Non_closed_number -> None

(***********************************************************************)
(* Declaring interpreters and uninterpreters for Z *)

let _ = Symbols.declare_numeral_interpreter "Z_scope"
  ["Coq";"ZArith";"fast_integer"]
  (z_of_int,Some pat_z_of_int)
  ([RRef (dummy_loc, glob_ZERO); 
    RRef (dummy_loc, glob_POS); 
    RRef (dummy_loc, glob_NEG)],
  uninterp_z,
  None)
