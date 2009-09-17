(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pcoq
open Pp
open Util
open Names
open Topconstr
open Libnames
open Bigint

exception Non_closed_number

(**********************************************************************)
(* Parsing positive via scopes                                        *)
(**********************************************************************)

open Libnames
open Rawterm
let make_dir l = make_dirpath (List.map id_of_string (List.rev l))
let positive_module = ["Coq";"NArith";"BinPos"]
let make_path dir id = Libnames.make_path (make_dir dir) (id_of_string id)

let positive_path = make_path positive_module "positive"

(* TODO: temporary hack *)
let make_kn dir id = Libnames.encode_kn dir id

let positive_kn =
  make_kn (make_dir positive_module) (id_of_string "positive")
let glob_positive = IndRef (positive_kn,0)
let path_of_xI = ((positive_kn,0),1)
let path_of_xO = ((positive_kn,0),2)
let path_of_xH = ((positive_kn,0),3)
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
      | (q,true) when q <> zero -> RApp (dloc,ref_xI,[pos_of q])
      | (q,true) -> ref_xH
  in
  pos_of x

let error_non_positive dloc =
  user_err_loc (dloc, "interp_positive",
    str "Only strictly positive numbers in type \"positive\".")

let interp_positive dloc n =
  if is_strictly_pos n then pos_of_bignat dloc n
  else error_non_positive dloc

(**********************************************************************)
(* Printing positive via scopes                                       *)
(**********************************************************************)

let rec bignat_of_pos = function
  | RApp (_, RRef (_,b),[a]) when b = glob_xO -> mult_2(bignat_of_pos a)
  | RApp (_, RRef (_,b),[a]) when b = glob_xI -> add_1(mult_2(bignat_of_pos a))
  | RRef (_, a) when a = glob_xH -> Bigint.one
  | _ -> raise Non_closed_number

let uninterp_positive p =
  try
    Some (bignat_of_pos p)
  with Non_closed_number ->
    None

(************************************************************************)
(* Declaring interpreters and uninterpreters for positive *)
(************************************************************************)

let _ = Notation.declare_numeral_interpreter "positive_scope"
  (positive_path,positive_module)
  interp_positive
  ([RRef (dummy_loc, glob_xI);
    RRef (dummy_loc, glob_xO);
    RRef (dummy_loc, glob_xH)],
   uninterp_positive,
   true)

(**********************************************************************)
(* Parsing N via scopes                                               *)
(**********************************************************************)

let binnat_module = ["Coq";"NArith";"BinNat"]
let n_kn = make_kn (make_dir binnat_module) (id_of_string "N")
let glob_n = IndRef (n_kn,0)
let path_of_N0 = ((n_kn,0),1)
let path_of_Npos = ((n_kn,0),2)
let glob_N0 = ConstructRef path_of_N0
let glob_Npos = ConstructRef path_of_Npos

let n_path = make_path binnat_module "N"

let n_of_binnat dloc pos_or_neg n =
  if n <> zero then
    RApp(dloc, RRef (dloc,glob_Npos), [pos_of_bignat dloc n])
  else
    RRef (dloc, glob_N0)

let error_negative dloc =
  user_err_loc (dloc, "interp_N", str "No negative numbers in type \"N\".")

let n_of_int dloc n =
  if is_pos_or_zero n then n_of_binnat dloc true n
  else error_negative dloc

(**********************************************************************)
(* Printing N via scopes                                              *)
(**********************************************************************)

let bignat_of_n = function
  | RApp (_, RRef (_,b),[a]) when b = glob_Npos -> bignat_of_pos a
  | RRef (_, a) when a = glob_N0 -> Bigint.zero
  | _ -> raise Non_closed_number

let uninterp_n p =
  try Some (bignat_of_n p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for N *)

let _ = Notation.declare_numeral_interpreter "N_scope"
  (n_path,binnat_module)
  n_of_int
  ([RRef (dummy_loc, glob_N0);
    RRef (dummy_loc, glob_Npos)],
  uninterp_n,
  true)

(**********************************************************************)
(* Parsing Z via scopes                                               *)
(**********************************************************************)

let binint_module = ["Coq";"ZArith";"BinInt"]
let z_path = make_path binint_module "Z"
let z_kn = make_kn (make_dir binint_module) (id_of_string "Z")
let glob_z = IndRef (z_kn,0)
let path_of_ZERO = ((z_kn,0),1)
let path_of_POS = ((z_kn,0),2)
let path_of_NEG = ((z_kn,0),3)
let glob_ZERO = ConstructRef path_of_ZERO
let glob_POS = ConstructRef path_of_POS
let glob_NEG = ConstructRef path_of_NEG

let z_of_int dloc n =
  if n <> zero then
    let sgn, n =
      if is_pos_or_zero n then glob_POS, n else glob_NEG, Bigint.neg n in
    RApp(dloc, RRef (dloc,sgn), [pos_of_bignat dloc n])
  else
    RRef (dloc, glob_ZERO)

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z = function
  | RApp (_, RRef (_,b),[a]) when b = glob_POS -> bignat_of_pos a
  | RApp (_, RRef (_,b),[a]) when b = glob_NEG -> Bigint.neg (bignat_of_pos a)
  | RRef (_, a) when a = glob_ZERO -> Bigint.zero
  | _ -> raise Non_closed_number

let uninterp_z p =
  try
    Some (bigint_of_z p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for Z *)

let _ = Notation.declare_numeral_interpreter "Z_scope"
  (z_path,binint_module)
  z_of_int
  ([RRef (dummy_loc, glob_ZERO);
    RRef (dummy_loc, glob_POS);
    RRef (dummy_loc, glob_NEG)],
  uninterp_z,
  true)
