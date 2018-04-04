(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Bigint

(* Poor's man DECLARE PLUGIN *)
let __coq_plugin_name = "positive_syntax_plugin"
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
  let ref_xI = DAst.make ?loc @@ GRef (glob_xI, None) in
  let ref_xH = DAst.make ?loc @@ GRef (glob_xH, None) in
  let ref_xO = DAst.make ?loc @@ GRef (glob_xO, None) in
  let rec pos_of x =
    match div2_with_rest x with
      | (q,false) -> DAst.make ?loc @@ GApp (ref_xO,[pos_of q])
      | (q,true) when not (Bigint.equal q zero) -> DAst.make ?loc @@ GApp (ref_xI,[pos_of q])
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

let is_gr c gr = match DAst.get c with
| GRef (r, _) -> GlobRef.equal r gr
| _ -> false

let rec bignat_of_pos x = DAst.with_val (function
  | GApp (r ,[a]) when is_gr r glob_xO -> mult_2(bignat_of_pos a)
  | GApp (r ,[a]) when is_gr r glob_xI -> add_1(mult_2(bignat_of_pos a))
  | GRef (a, _)                when GlobRef.equal a glob_xH -> Bigint.one
  | _ -> raise Non_closed_number
  ) x

let uninterp_positive (AnyGlobConstr p) =
  try
    Some (bignat_of_pos p)
  with Non_closed_number ->
    None

(************************************************************************)
(* Declaring interpreters and uninterpreters for positive *)
(************************************************************************)

open Notation

let at_declare_ml_module f x =
  Mltop.declare_cache_obj (fun () -> f x) __coq_plugin_name

let _ =
  let scope = "positive_scope" in
  register_bignumeral_interpretation scope (interp_positive,uninterp_positive);
  at_declare_ml_module enable_prim_token_interpretation
    { pt_scope = scope;
      pt_uid = scope;
      pt_required = (positive_path,binnums);
      pt_refs = [glob_xI; glob_xO; glob_xH];
      pt_in_match = true }
