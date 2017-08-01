(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Globnames
open Glob_term
open Bigint

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "r_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

exception Non_closed_number

(**********************************************************************)
(* Parsing positive via scopes                                        *)
(**********************************************************************)

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
  let ref_xI = CAst.make @@ GRef (glob_xI, None) in
  let ref_xH = CAst.make @@ GRef (glob_xH, None) in
  let ref_xO = CAst.make @@ GRef (glob_xO, None) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> CAst.make @@ GApp (ref_xO,[pos_of q])
      | (q,true) when not (Bigint.equal q zero) -> CAst.make @@ GApp (ref_xI,[pos_of q])
      | (q,true) -> ref_xH
  in
  pos_of x

(**********************************************************************)
(* Printing positive via scopes                                       *)
(**********************************************************************)

let rec bignat_of_pos = function
  | { CAst.v = GApp ({ CAst.v = GRef (b,_)},[a]) } when Globnames.eq_gr b glob_xO -> mult_2(bignat_of_pos a)
  | { CAst.v = GApp ({ CAst.v = GRef (b,_)},[a]) } when Globnames.eq_gr b glob_xI -> add_1(mult_2(bignat_of_pos a))
  | { CAst.v = GRef (a, _) } when Globnames.eq_gr a glob_xH -> Bigint.one
  | _ -> raise Non_closed_number

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
    CAst.make @@ GApp(CAst.make @@ GRef (sgn,None), [pos_of_bignat ?loc n])
  else
    CAst.make @@ GRef (glob_ZERO, None)

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z = function
  | { CAst.v = GApp ({ CAst.v = GRef (b,_)},[a]) } when Globnames.eq_gr b glob_POS -> bignat_of_pos a
  | { CAst.v = GApp ({ CAst.v = GRef (b,_)},[a]) } when Globnames.eq_gr b glob_NEG -> Bigint.neg (bignat_of_pos a)
  | { CAst.v = GRef (a, _) } when Globnames.eq_gr a glob_ZERO -> Bigint.zero
  | _ -> raise Non_closed_number

(**********************************************************************)
(* Parsing R via scopes                                               *)
(**********************************************************************)

let rdefinitions = ["Coq";"Reals";"Rdefinitions"]
let r_path = make_path rdefinitions "R"

(* TODO: temporary hack *)
let make_path dir id = Globnames.encode_con dir (Id.of_string id)

let glob_IZR = ConstRef (make_path (make_dir rdefinitions) "IZR")

let r_of_int ?loc z =
  CAst.make @@ GApp (CAst.make @@ GRef(glob_IZR,None), [z_of_int ?loc z])

(**********************************************************************)
(* Printing R via scopes                                              *)
(**********************************************************************)

let bigint_of_r = function
  | { CAst.v = GApp ({ CAst.v = GRef (o,_) }, [a]) } when Globnames.eq_gr o glob_IZR ->
      bigint_of_z a
  | _ -> raise Non_closed_number

let uninterp_r p =
  try
    Some (bigint_of_r p)
  with Non_closed_number ->
    None

let _ = Notation.declare_numeral_interpreter "R_scope"
  (r_path,["Coq";"Reals";"Rdefinitions"])
  r_of_int
  ([CAst.make @@ GRef (glob_IZR, None)],
    uninterp_r,
    false)
