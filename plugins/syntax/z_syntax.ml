(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Bigint
open Positive_syntax_plugin.Positive_syntax

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "z_syntax_plugin"
let () = Mltop.add_known_module __coq_plugin_name

(**********************************************************************)
(* Parsing Z via scopes                                               *)
(**********************************************************************)

open Globnames
open Glob_term

let binnums = ["Coq";"Numbers";"BinNums"]

let make_dir l = DirPath.make (List.rev_map Id.of_string l)
let make_path dir id = Libnames.make_path (make_dir dir) (Id.of_string id)

(* TODO: temporary hack *)
let make_kn dir id = Globnames.encode_mind dir id

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
    DAst.make ?loc @@ GApp(DAst.make ?loc @@ GRef(sgn,None), [pos_of_bignat ?loc n])
  else
    DAst.make ?loc @@ GRef(glob_ZERO, None)

(**********************************************************************)
(* Printing Z via scopes                                              *)
(**********************************************************************)

let bigint_of_z z = DAst.with_val (function
  | GApp (r, [a]) when is_gr r glob_POS -> bignat_of_pos a
  | GApp (r, [a]) when is_gr r glob_NEG -> Bigint.neg (bignat_of_pos a)
  | GRef (a, _) when GlobRef.equal a glob_ZERO -> Bigint.zero
  | _ -> raise Non_closed_number
  ) z

let uninterp_z (AnyGlobConstr p) =
  try
    Some (bigint_of_z p)
  with Non_closed_number -> None

(************************************************************************)
(* Declaring interpreters and uninterpreters for Z *)

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let _ =
  let scope = "Z_scope" in
  register_bignumeral_interpretation scope (z_of_int,uninterp_z);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_scope = scope;
      pt_uid = scope;
      pt_required = (z_path,binnums);
      pt_refs = [glob_ZERO; glob_POS; glob_NEG];
      pt_in_match = true }
