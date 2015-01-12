(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Declarations
open Libnames
open Constrexpr
open Constrintern
open Misctypes

type module_internalization_error =
  | NotAModuleNorModtype of string
  | IncorrectWithInModule
  | IncorrectModuleApplication

exception ModuleInternalizationError of module_internalization_error

let error_not_a_module_loc kind loc qid =
  let s = string_of_qualid qid in
  let e = match kind with
    | Module -> Modops.ModuleTypingError (Modops.NotAModule s)
    | ModType -> Modops.ModuleTypingError (Modops.NotAModuleType s)
    | ModAny -> ModuleInternalizationError (NotAModuleNorModtype s)
  in
  Loc.raise loc e

let error_application_to_not_path loc me =
  Loc.raise loc (Modops.ModuleTypingError (Modops.ApplicationToNotPath me))

let error_incorrect_with_in_module loc =
  Loc.raise loc (ModuleInternalizationError IncorrectWithInModule)

let error_application_to_module_type loc =
  Loc.raise loc (ModuleInternalizationError IncorrectModuleApplication)

(** Searching for a module name in the Nametab.

    According to the input module kind, modules or module types
    or both are searched. The returned kind is never ModAny, and
    it is equal to the input kind when this one isn't ModAny. *)

let lookup_module_or_modtype kind (loc,qid) =
  try
    if kind == ModType then raise Not_found;
    let mp = Nametab.locate_module qid in
    Dumpglob.dump_modref loc mp "modtype"; (mp,Module)
  with Not_found ->
    try
      if kind == Module then raise Not_found;
      let mp = Nametab.locate_modtype qid in
      Dumpglob.dump_modref loc mp "mod"; (mp,ModType)
    with Not_found -> error_not_a_module_loc kind loc qid

let lookup_module lqid = fst (lookup_module_or_modtype Module lqid)

let transl_with_decl env = function
  | CWith_Module ((_,fqid),qid) ->
      WithMod (fqid,lookup_module qid)
  | CWith_Definition ((_,fqid),c) ->
      WithDef (fqid,fst (interp_constr env Evd.empty c)) (*FIXME*)

let loc_of_module = function
  | CMident (loc,_) | CMapply (loc,_,_) | CMwith (loc,_,_) -> loc

(* Invariant : the returned kind is never ModAny, and it is
   equal to the input kind when this one isn't ModAny. *)

let rec interp_module_ast env kind = function
  | CMident qid ->
      let (mp,kind) = lookup_module_or_modtype kind qid in
      (MEident mp, kind)
  | CMapply (_,me1,me2) ->
      let me1',kind1 = interp_module_ast env kind me1 in
      let me2',kind2 = interp_module_ast env ModAny me2 in
      let mp2 = match me2' with
        | MEident mp -> mp
        | _ -> error_application_to_not_path (loc_of_module me2) me2'
      in
      if kind2 == ModType then
        error_application_to_module_type (loc_of_module me2);
      (MEapply (me1',mp2), kind1)
  | CMwith (loc,me,decl) ->
      let me,kind = interp_module_ast env kind me in
      if kind == Module then error_incorrect_with_in_module loc;
      let decl = transl_with_decl env decl in
      (MEwith(me,decl), kind)
