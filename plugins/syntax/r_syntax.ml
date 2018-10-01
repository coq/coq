(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

let is_gr c gr = match DAst.get c with
| GRef (r, _) -> GlobRef.equal r gr
| _ -> false

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
  let ref_xI = DAst.make @@ GRef (glob_xI, None) in
  let ref_xH = DAst.make @@ GRef (glob_xH, None) in
  let ref_xO = DAst.make @@ GRef (glob_xO, None) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> DAst.make @@ GApp (ref_xO,[pos_of q])
      | (q,true) when not (Bigint.equal q zero) -> DAst.make @@ GApp (ref_xI,[pos_of q])
      | (q,true) -> ref_xH
  in
  pos_of x

(**********************************************************************)
(* Printing positive via scopes                                       *)
(**********************************************************************)

let rec bignat_of_pos c = match DAst.get c with
  | GApp (r, [a]) when is_gr r glob_xO -> mult_2(bignat_of_pos a)
  | GApp (r, [a]) when is_gr r glob_xI -> add_1(mult_2(bignat_of_pos a))
  | GRef (a, _) when GlobRef.equal a glob_xH -> Bigint.one
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
    DAst.make @@ GApp(DAst.make @@ GRef (sgn,None), [pos_of_bignat ?loc n])
  else
    DAst.make @@ GRef (glob_ZERO, None)

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z c = match DAst.get c with
  | GApp (r,[a]) when is_gr r glob_POS -> bignat_of_pos a
  | GApp (r,[a]) when is_gr r glob_NEG -> Bigint.neg (bignat_of_pos a)
  | GRef (a, _) when GlobRef.equal a glob_ZERO -> Bigint.zero
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
  DAst.make @@ GApp (DAst.make @@ GRef(glob_IZR,None), [z_of_int ?loc z])

(**********************************************************************)
(* Printing R via scopes                                              *)
(**********************************************************************)

let bigint_of_r c = match DAst.get c with
  | GApp (r, [a]) when is_gr r glob_IZR ->
      bigint_of_z a
  | _ -> raise Non_closed_number

let uninterp_r (AnyGlobConstr p) =
  try
    Some (bigint_of_r p)
  with Non_closed_number ->
    None

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let r_scope = "R_scope"

let _ =
  register_bignumeral_interpretation r_scope (r_of_int,uninterp_r);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_local = false;
      pt_scope = r_scope;
      pt_interp_info = Uid r_scope;
      pt_required = (r_path,["Coq";"Reals";"Rdefinitions"]);
      pt_refs = [glob_IZR];
      pt_in_match = false }
