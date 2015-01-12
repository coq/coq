(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Hugo Herbelin from code formerly dispatched in
   syntax_def.ml or tacinterp.ml, Sep 2009 *)

(* This file provides high-level name globalization functions *)

(* *)
open Pp
open Errors
open Libnames
open Globnames
open Misctypes
open Syntax_def
open Notation_term

let global_of_extended_global_head = function
  | TrueGlobal ref -> ref
  | SynDef kn ->
      let _, syn_def = search_syntactic_definition kn in
      let rec head_of = function
        | NRef ref -> ref
        | NApp (rc, _) -> head_of rc
        | NCast (rc, _) -> head_of rc
        | NLetIn (_, _, rc) -> head_of rc
        | _ -> raise Not_found in
      head_of syn_def

let global_of_extended_global = function
  | TrueGlobal ref -> ref
  | SynDef kn ->
  match search_syntactic_definition kn with
  | [],NRef ref -> ref
  | [],NApp (NRef ref,[]) -> ref
  | _ -> raise Not_found

let locate_global_with_alias ?(head=false) (loc,qid) =
  let ref = Nametab.locate_extended qid in
  try
    if head then global_of_extended_global_head ref
    else global_of_extended_global ref
  with Not_found ->
    user_err_loc (loc,"",pr_qualid qid ++
      str " is bound to a notation that does not denote a reference.")

let global_inductive_with_alias r =
  let (loc,qid as lqid) = qualid_of_reference r in
  try match locate_global_with_alias lqid with
  | IndRef ind -> ind
  | ref ->
      user_err_loc (loc_of_reference r,"global_inductive",
        pr_reference r ++ spc () ++ str "is not an inductive type.")
  with Not_found -> Nametab.error_global_not_found_loc loc qid

let global_with_alias ?head r =
  let (loc,qid as lqid) = qualid_of_reference r in
  try locate_global_with_alias ?head lqid
  with Not_found -> Nametab.error_global_not_found_loc loc qid

let smart_global ?head = function
  | AN r ->
      global_with_alias ?head r
  | ByNotation (loc,ntn,sc) ->
      Notation.interp_notation_as_global_reference loc (fun _ -> true) ntn sc

let smart_global_inductive = function
  | AN r ->
      global_inductive_with_alias r
  | ByNotation (loc,ntn,sc) ->
      destIndRef
        (Notation.interp_notation_as_global_reference loc isIndRef ntn sc)

let loc_of_smart_reference = function
  | AN r -> loc_of_reference r
  | ByNotation (loc,_,_) -> loc
