(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Libnames
open Constrexpr
open Constrintern
open Declaremods

type module_internalization_error =
  | NotAModuleNorModtype of string
  | IncorrectWithInModule
  | IncorrectModuleApplication

exception ModuleInternalizationError of module_internalization_error

let error_not_a_module_loc kind loc qid =
  let s = string_of_qualid qid in
  let e = let open Declaremods in match kind with
    | Module -> Modops.ModuleTypingError (Modops.NotAModule s)
    | ModType -> Modops.ModuleTypingError (Modops.NotAModuleType s)
    | ModAny -> ModuleInternalizationError (NotAModuleNorModtype s)
  in
  Loc.raise ?loc e

let error_application_to_not_path loc me =
  Loc.raise ?loc (Modops.ModuleTypingError (Modops.ApplicationToNotPath me))

let error_incorrect_with_in_module loc =
  Loc.raise ?loc (ModuleInternalizationError IncorrectWithInModule)

let error_application_to_module_type loc =
  Loc.raise ?loc (ModuleInternalizationError IncorrectModuleApplication)

(** Searching for a module name in the Nametab.

    According to the input module kind, modules or module types
    or both are searched. The returned kind is never ModAny, and
    it is equal to the input kind when this one isn't ModAny. *)

let lookup_module_or_modtype kind qid =
  let open Declaremods in
  let loc = qid.CAst.loc in
  try
    if kind == ModType then raise Not_found;
    let mp = Nametab.locate_module qid in
    Dumpglob.dump_modref ?loc mp "modtype"; (mp,Module)
  with Not_found ->
    try
      if kind == Module then raise Not_found;
      let mp = Nametab.locate_modtype qid in
      Dumpglob.dump_modref ?loc mp "mod"; (mp,ModType)
    with Not_found -> error_not_a_module_loc kind loc qid

let lookup_module lqid = fst (lookup_module_or_modtype Module lqid)

let lookup_polymorphism env base kind fqid =
  let m = match kind with
    | Module -> (Environ.lookup_module base env).mod_type
    | ModType -> (Environ.lookup_modtype base env).mod_type
    | ModAny -> assert false
  in
  let rec defunctor = function
    | NoFunctor m -> m
    | MoreFunctor (_,_,m) -> defunctor m
  in
  let rec aux m fqid =
    let open Names in
    match fqid with
    | [] -> assert false
    | [id] ->
      let test (lab,obj) =
        match Id.equal (Label.to_id lab) id, obj with
        | false, _ | _, (SFBmodule _ | SFBmodtype _) -> None
        | true, SFBmind mind -> Some (Declareops.inductive_is_polymorphic mind)
        | true, SFBconst const -> Some (Declareops.constant_is_polymorphic const)
      in
      (try CList.find_map test m with Not_found -> false (* error later *))
    | id::rem ->
      let next = function
        | MoreFunctor _ -> false (* error later *)
        | NoFunctor body -> aux body rem
      in
      let test (lab,obj) =
        match Id.equal (Label.to_id lab) id, obj with
        | false, _ | _, (SFBconst _ | SFBmind _) -> None
        | true, SFBmodule body -> Some (next body.mod_type)
        | true, SFBmodtype body ->  (* XXX is this valid? If not error later *)
          Some (next body.mod_type)
      in
      (try CList.find_map test m with Not_found -> false (* error later *))
  in
  aux (defunctor m) fqid

let transl_with_decl env base kind = function
  | CWith_Module ({CAst.v=fqid},qid) ->
      WithMod (fqid,lookup_module qid), Univ.ContextSet.empty
  | CWith_Definition ({CAst.v=fqid},udecl,c) ->
    let sigma, udecl = Constrexpr_ops.interp_univ_decl_opt env udecl in
    let c, ectx = interp_constr env sigma c in
    let poly = lookup_polymorphism env base kind fqid in
    begin match UState.check_univ_decl ~poly ectx udecl with
      | Entries.Polymorphic_entry (nas, ctx) ->
        let inst, ctx = Univ.abstract_universes nas ctx in
        let c = EConstr.Vars.subst_univs_level_constr (Univ.make_instance_subst inst) c in
        let c = EConstr.to_constr sigma c in
        WithDef (fqid,(c, Some ctx)), Univ.ContextSet.empty
      | Entries.Monomorphic_entry ctx ->
        let c = EConstr.to_constr sigma c in
        WithDef (fqid,(c, None)), ctx
    end

let loc_of_module l = l.CAst.loc

(* Invariant : the returned kind is never ModAny, and it is
   equal to the input kind when this one isn't ModAny. *)

let rec interp_module_ast env kind m cst = match m with
  | {CAst.loc;v=CMident qid} ->
      let (mp,kind) = lookup_module_or_modtype kind qid in
      (MEident mp, mp, kind, cst)
  | {CAst.loc;v=CMapply (me1,me2)} ->
      let me1', base, kind1, cst = interp_module_ast env kind me1 cst in
      let me2', _, kind2, cst = interp_module_ast env ModAny me2 cst in
      let mp2 = match me2' with
        | MEident mp -> mp
        | _ -> error_application_to_not_path (loc_of_module me2) me2'
      in
      if kind2 == ModType then
        error_application_to_module_type (loc_of_module me2);
      (MEapply (me1',mp2), base, kind1, cst)
  | {CAst.loc;v=CMwith (me,decl)} ->
      let me,base,kind,cst = interp_module_ast env kind me cst in
      if kind == Module then error_incorrect_with_in_module m.CAst.loc;
      let decl, cst' = transl_with_decl env base kind decl in
      let cst = Univ.ContextSet.union cst cst' in
      (MEwith(me,decl), base, kind, cst)

let interp_module_ast env kind m =
  let me, _, kind, cst = interp_module_ast env kind m Univ.ContextSet.empty in
  me, kind, cst
