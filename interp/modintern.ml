(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Libnames
open Constrexpr
open Constrintern

type module_internalization_error =
  | NotAModuleNorModtype of qualid
  | NotAModuleType of qualid
  | NotAModule of qualid
  | IncorrectWithInModule
  | IncorrectModuleApplication

exception ModuleInternalizationError of module_internalization_error

type module_kind = Module | ModType | ModAny

let error_not_a_module_loc ~info kind loc qid =
  let e = match kind with
    | Module -> NotAModule qid
    | ModType -> NotAModuleType qid
    | ModAny -> NotAModuleNorModtype qid
  in
  let info = Option.cata (Loc.add_loc info) info loc in
  Exninfo.iraise (ModuleInternalizationError e,info)

let error_incorrect_with_in_module loc =
  Loc.raise ?loc (ModuleInternalizationError IncorrectWithInModule)

let error_application_to_module_type loc =
  Loc.raise ?loc (ModuleInternalizationError IncorrectModuleApplication)

(** Searching for a module name in the Nametab.

    According to the input module kind, modules or module types
    or both are searched. The returned kind is never ModAny, and
    it is equal to the input kind when this one isn't ModAny. *)

let lookup_module_or_modtype kind qid =
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
    with Not_found as exn ->
      let _, info = Exninfo.capture exn in
      error_not_a_module_loc ~info kind loc qid

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

let intern_with_decl = function
  | CWith_Module ({CAst.v=fqid},qid) ->
    WithMod (fqid,lookup_module qid)
  | CWith_Definition ({CAst.v=fqid},udecl,c) ->
    WithDef (fqid,(udecl,c))

let loc_of_module l = l.CAst.loc

(* Invariant : the returned kind is never ModAny, and it is
   equal to the input kind when this one isn't ModAny. *)

let rec intern_module_ast kind m = match m with
  | {CAst.loc;v=CMident qid} ->
      let (mp,kind) = lookup_module_or_modtype kind qid in
      (MEident mp, mp, kind)
  | {CAst.loc;v=CMapply (me1,me2)} ->
      let me1', base, kind1 = intern_module_ast kind me1 in
      let mp2, kind2 = lookup_module_or_modtype ModAny me2 in
      if kind2 == ModType then
        error_application_to_module_type (loc_of_module me2);
      (MEapply (me1',mp2), base, kind1)
  | {CAst.loc;v=CMwith (me,decl)} ->
      let me,base,kind = intern_module_ast kind me in
      if kind == Module then error_incorrect_with_in_module m.CAst.loc;
      let decl = intern_with_decl decl in
      (MEwith(me,decl), base, kind)

let interp_with_decl env base kind = function
  | WithMod (fqid,mp) -> WithMod (fqid,mp), Univ.ContextSet.empty
  | WithDef(fqid,(udecl,c)) ->
    let sigma, udecl = interp_univ_decl_opt env udecl in
    let c, ectx = interp_constr env sigma c in
    let poly = lookup_polymorphism env base kind fqid in
    begin match fst (UState.check_univ_decl ~poly ectx udecl) with
      | UState.Polymorphic_entry ctx ->
        let inst, ctx = Univ.abstract_universes ctx in
        let c = EConstr.Vars.subst_univs_level_constr (Univ.make_instance_subst inst) c in
        let c = EConstr.to_constr sigma c in
        WithDef (fqid,(c, Some ctx)), Univ.ContextSet.empty
      | UState.Monomorphic_entry ctx ->
        let c = EConstr.to_constr sigma c in
        WithDef (fqid,(c, None)), ctx
    end

let rec interp_module_ast env kind base m cst = match m with
| MEident mp ->
  MEident mp, cst
| MEapply (me,mp) ->
  let me', cst = interp_module_ast env kind base me cst in
  MEapply(me',mp), cst
| MEwith(me,decl) ->
  let me, cst = interp_module_ast env kind base me cst in
  let decl, cst' = interp_with_decl env base kind decl in
  let cst = Univ.ContextSet.union cst cst' in
  MEwith(me,decl), cst

let interp_module_ast env kind base m =
  interp_module_ast env kind base m Univ.ContextSet.empty
