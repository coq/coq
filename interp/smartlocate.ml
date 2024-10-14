(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Abbreviation
open Notation_term

let global_of_extended_global_head = function
  | TrueGlobal ref -> ref
  | Abbrev kn ->
      let _, syn_def = search_abbreviation kn in
      let rec head_of = function
        | NRef (ref,None) -> ref
        | NApp (rc, _) -> head_of rc
        | NCast (rc, _, _) -> head_of rc
        | NLetIn (_, _, _, rc) -> head_of rc
        | _ -> raise Not_found in
      head_of syn_def

let global_of_extended_global_exn = function
  | TrueGlobal ref -> ref
  | Abbrev kn ->
  match search_abbreviation kn with
  | [],NRef (ref,None) -> ref
  | [],NApp (NRef (ref,None),[]) -> ref
  | _ -> raise Not_found

let locate_global_with_alias ?(head=false) qid =
  let ref = Nametab.locate_extended qid in
  try
    if head then global_of_extended_global_head ref
    else global_of_extended_global_exn ref
  with Not_found ->
    user_err ?loc:qid.CAst.loc (pr_qualid qid ++
      str " is bound to a notation that does not denote a reference.")

let global_of_extended_global x =
  try Some (global_of_extended_global_exn x)
  with Not_found -> None

let global_constant_with_alias qid  =
  try match locate_global_with_alias qid with
  | Names.GlobRef.ConstRef c -> c
  | ref ->
      user_err ?loc:qid.CAst.loc
        (pr_qualid qid ++ spc () ++ str "is not a reference to a constant.")
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info qid

let global_inductive_with_alias qid  =
  try match locate_global_with_alias qid with
  | Names.GlobRef.IndRef ind -> ind
  | ref ->
      user_err ?loc:qid.CAst.loc
        (pr_qualid qid ++ spc () ++ str "is not an inductive type.")
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info qid

let global_constructor_with_alias qid  =
  try match locate_global_with_alias qid with
  | Names.GlobRef.ConstructRef c -> c
  | ref ->
      user_err ?loc:qid.CAst.loc
        (pr_qualid qid ++ spc () ++ str "is not a constructor of an inductive type.")
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info qid

let global_with_alias ?head qid =
  try locate_global_with_alias ?head qid
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    Nametab.error_global_not_found ~info qid

let smart_global ?(head = false) = let open Constrexpr in CAst.with_loc_val (fun ?loc -> function
  | AN r ->
    global_with_alias ~head r
  | ByNotation (ntn,sc) ->
    Notation.interp_notation_as_global_reference ?loc ~head (fun _ -> true) ntn sc)

let smart_global_kind f dest is = let open Constrexpr in CAst.with_loc_val (fun ?loc -> function
  | AN r -> f r
  | ByNotation (ntn,sc) ->
    dest
      (Notation.interp_notation_as_global_reference ?loc ~head:false is ntn sc))

let smart_global_constant =
  smart_global_kind global_constant_with_alias destConstRef isConstRef

let smart_global_inductive =
  smart_global_kind global_inductive_with_alias destIndRef isIndRef

let smart_global_constructor =
  smart_global_kind global_constructor_with_alias destConstructRef isConstructRef
