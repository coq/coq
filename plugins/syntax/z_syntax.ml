(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Bigint

exception Non_closed_number

(**********************************************************************)
(* Parsing positive via scopes                                        *)
(**********************************************************************)

open Globnames
open Glob_term

let binnums = ["Coq";"Numbers";"BinNums"]

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

let positive_path = make_path binnums "positive"

(* TODO: temporary hack *)
let make_kn dir id = Globnames.encode_mind dir id

let positive_kn = make_kn (make_dir binnums) (Id.of_string "positive")
let glob_positive = IndRef (positive_kn,0)
let path_of_xI = ((positive_kn,0),1)
let path_of_xO = ((positive_kn,0),2)
let path_of_xH = ((positive_kn,0),3)
let glob_xI = ConstructRef path_of_xI
let glob_xO = ConstructRef path_of_xO
let glob_xH = ConstructRef path_of_xH

let pos_of_bignat dloc x =
  let ref_xI = GRef (dloc, glob_xI, None) in
  let ref_xH = GRef (dloc, glob_xH, None) in
  let ref_xO = GRef (dloc, glob_xO, None) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> GApp (dloc, ref_xO,[pos_of q])
      | (q,true) when not (Bigint.equal q zero) -> GApp (dloc,ref_xI,[pos_of q])
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
  | GApp (_, GRef (_,b,_),[a]) when Globnames.eq_gr b glob_xO -> mult_2(bignat_of_pos a)
  | GApp (_, GRef (_,b,_),[a]) when Globnames.eq_gr b glob_xI -> add_1(mult_2(bignat_of_pos a))
  | GRef (_, a, _) when Globnames.eq_gr a glob_xH -> Bigint.one
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
  (positive_path,binnums)
  interp_positive
  ([GRef (Loc.ghost, glob_xI, None);
    GRef (Loc.ghost, glob_xO, None);
    GRef (Loc.ghost, glob_xH, None)],
   uninterp_positive,
   true)

(**********************************************************************)
(* Parsing N via scopes                                               *)
(**********************************************************************)

let n_kn = make_kn (make_dir binnums) (Id.of_string "N")
let glob_n = IndRef (n_kn,0)
let path_of_N0 = ((n_kn,0),1)
let path_of_Npos = ((n_kn,0),2)
let glob_N0 = ConstructRef path_of_N0
let glob_Npos = ConstructRef path_of_Npos

let n_path = make_path binnums "N"

let n_of_binnat dloc pos_or_neg n =
  if not (Bigint.equal n zero) then
    GApp(dloc, GRef (dloc,glob_Npos,None), [pos_of_bignat dloc n])
  else
    GRef (dloc, glob_N0, None)

let error_negative dloc =
  user_err_loc (dloc, "interp_N", str "No negative numbers in type \"N\".")

let n_of_int dloc n =
  if is_pos_or_zero n then n_of_binnat dloc true n
  else error_negative dloc

(**********************************************************************)
(* Printing N via scopes                                              *)
(**********************************************************************)

let bignat_of_n = function
  | GApp (_, GRef (_,b,_),[a]) when Globnames.eq_gr b glob_Npos -> bignat_of_pos a
  | GRef (_, a,_) when Globnames.eq_gr a glob_N0 -> Bigint.zero
  | _ -> raise Non_closed_number

let uninterp_n p =
  try Some (bignat_of_n p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for N *)

let _ = Notation.declare_numeral_interpreter "N_scope"
  (n_path,binnums)
  n_of_int
  ([GRef (Loc.ghost, glob_N0, None);
    GRef (Loc.ghost, glob_Npos, None)],
  uninterp_n,
  true)

(**********************************************************************)
(* Parsing Z via scopes                                               *)
(**********************************************************************)

let z_path = make_path binnums "Z"
let z_kn = make_kn (make_dir binnums) (Id.of_string "Z")
let glob_z = IndRef (z_kn,0)
let path_of_ZERO = ((z_kn,0),1)
let path_of_POS = ((z_kn,0),2)
let path_of_NEG = ((z_kn,0),3)
let glob_ZERO = ConstructRef path_of_ZERO
let glob_POS = ConstructRef path_of_POS
let glob_NEG = ConstructRef path_of_NEG

let z_of_int dloc n =
  if not (Bigint.equal n zero) then
    let sgn, n =
      if is_pos_or_zero n then glob_POS, n else glob_NEG, Bigint.neg n in
    GApp(dloc, GRef (dloc,sgn,None), [pos_of_bignat dloc n])
  else
    GRef (dloc, glob_ZERO, None)

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z = function
  | GApp (_, GRef (_,b,_),[a]) when Globnames.eq_gr b glob_POS -> bignat_of_pos a
  | GApp (_, GRef (_,b,_),[a]) when Globnames.eq_gr b glob_NEG -> Bigint.neg (bignat_of_pos a)
  | GRef (_, a, _) when Globnames.eq_gr a glob_ZERO -> Bigint.zero
  | _ -> raise Non_closed_number

let uninterp_z p =
  try
    Some (bigint_of_z p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for Z *)

let _ = Notation.declare_numeral_interpreter "Z_scope"
  (z_path,binnums)
  z_of_int
  ([GRef (Loc.ghost, glob_ZERO, None);
    GRef (Loc.ghost, glob_POS, None);
    GRef (Loc.ghost, glob_NEG, None)],
  uninterp_z,
  true)
