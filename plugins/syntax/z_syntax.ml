(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Bigint

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "z_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

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

let pos_of_bignat ?loc x = 
  let ref_xI = CAst.make ?loc @@ GRef (glob_xI, None) in
  let ref_xH = CAst.make ?loc @@ GRef (glob_xH, None) in
  let ref_xO = CAst.make ?loc @@ GRef (glob_xO, None) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> CAst.make ?loc @@ GApp (ref_xO,[pos_of q])
      | (q,true) when not (Bigint.equal q zero) -> CAst.make ?loc @@ GApp (ref_xI,[pos_of q])
      | (q,true) -> ref_xH
  in
  pos_of x

let error_non_positive ?loc =
  user_err ?loc ~hdr:"interp_positive"
   (str "Only strictly positive numbers in type \"positive\".")

let interp_positive ?loc n =
  if is_strictly_pos n then pos_of_bignat ?loc n
  else error_non_positive ?loc

(**********************************************************************)
(* Printing positive via scopes                                       *)
(**********************************************************************)

let rec bignat_of_pos x = CAst.with_val (function
  | GApp ({ CAst.v = GRef (b,_) },[a]) when Globnames.eq_gr b glob_xO -> mult_2(bignat_of_pos a)
  | GApp ({ CAst.v = GRef (b,_) },[a]) when Globnames.eq_gr b glob_xI -> add_1(mult_2(bignat_of_pos a))
  | GRef (a, _)                when Globnames.eq_gr a glob_xH -> Bigint.one
  | _ -> raise Non_closed_number
  ) x

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
  ([CAst.make @@ GRef (glob_xI, None);
    CAst.make @@ GRef (glob_xO, None);
    CAst.make @@ GRef (glob_xH, None)],
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

let n_of_binnat ?loc pos_or_neg n = CAst.make ?loc @@
  if not (Bigint.equal n zero) then
    GApp(CAst.make @@ GRef (glob_Npos,None), [pos_of_bignat ?loc n])
  else
    GRef(glob_N0, None)

let error_negative ?loc =
  user_err ?loc ~hdr:"interp_N" (str "No negative numbers in type \"N\".")

let n_of_int ?loc n =
  if is_pos_or_zero n then n_of_binnat ?loc true n
  else error_negative ?loc

(**********************************************************************)
(* Printing N via scopes                                              *)
(**********************************************************************)

let bignat_of_n = CAst.with_val (function
  | GApp ({ CAst.v = GRef (b,_)},[a]) when Globnames.eq_gr b glob_Npos -> bignat_of_pos a
  | GRef (a,_) when Globnames.eq_gr a glob_N0 -> Bigint.zero
  | _ -> raise Non_closed_number
  )

let uninterp_n p =
  try Some (bignat_of_n p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for N *)

let _ = Notation.declare_numeral_interpreter "N_scope"
  (n_path,binnums)
  n_of_int
  ([CAst.make @@ GRef (glob_N0, None);
    CAst.make @@ GRef (glob_Npos, None)],
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

let z_of_int ?loc n =
  if not (Bigint.equal n zero) then
    let sgn, n =
      if is_pos_or_zero n then glob_POS, n else glob_NEG, Bigint.neg n in
    CAst.make ?loc @@ GApp(CAst.make ?loc @@ GRef(sgn,None), [pos_of_bignat ?loc n])
  else
    CAst.make ?loc @@ GRef(glob_ZERO, None)

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z = CAst.with_val (function
  | GApp ({ CAst.v = GRef (b,_)},[a]) when Globnames.eq_gr b glob_POS -> bignat_of_pos a
  | GApp ({ CAst.v = GRef (b,_)},[a]) when Globnames.eq_gr b glob_NEG -> Bigint.neg (bignat_of_pos a)
  | GRef (a, _) when Globnames.eq_gr a glob_ZERO -> Bigint.zero
  | _ -> raise Non_closed_number
  )

let uninterp_z p =
  try
    Some (bigint_of_z p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for Z *)

let _ = Notation.declare_numeral_interpreter "Z_scope"
  (z_path,binnums)
  z_of_int
  ([CAst.make @@ GRef (glob_ZERO, None);
    CAst.make @@ GRef (glob_POS, None);
    CAst.make @@ GRef (glob_NEG, None)],
  uninterp_z,
  true)
