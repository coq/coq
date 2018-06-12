(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from code formerly dispatched in
   syntax_def.ml or tacinterp.ml, Sep 2009 *)

(* This file provides high-level name globalization functions *)

(* *)
open Pp
open CErrors
open Libnames
open Globnames
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
        | NLetIn (_, _, _, rc) -> head_of rc
        | _ -> raise Not_found in
      head_of syn_def

let global_of_extended_global = function
  | TrueGlobal ref -> ref
  | SynDef kn ->
  match search_syntactic_definition kn with
  | [],NRef ref -> ref
  | [],NApp (NRef ref,[]) -> ref
  | _ -> raise Not_found

let locate_global_with_alias ?(head=false) qid =
  let ref = Nametab.locate_extended qid in
  try
    if head then global_of_extended_global_head ref
    else global_of_extended_global ref
  with Not_found ->
    user_err ?loc:qid.CAst.loc (pr_qualid qid ++
      str " is bound to a notation that does not denote a reference.")

let global_inductive_with_alias qid  =
  try match locate_global_with_alias qid with
  | IndRef ind -> ind
  | ref ->
      user_err ?loc:qid.CAst.loc ~hdr:"global_inductive"
        (pr_qualid qid ++ spc () ++ str "is not an inductive type.")
  with Not_found -> Nametab.error_global_not_found qid

let global_with_alias ?head qid =
  try locate_global_with_alias ?head qid
  with Not_found -> Nametab.error_global_not_found qid

let smart_global ?head = let open Constrexpr in CAst.with_loc_val (fun ?loc -> function
  | AN r ->
    global_with_alias ?head r
  | ByNotation (ntn,sc) ->
    Notation.interp_notation_as_global_reference ?loc (fun _ -> true) ntn sc)

let smart_global_inductive = let open Constrexpr in CAst.with_loc_val (fun ?loc -> function
  | AN r ->
    global_inductive_with_alias r
  | ByNotation (ntn,sc) ->
    destIndRef
      (Notation.interp_notation_as_global_reference ?loc isIndRef ntn sc))
