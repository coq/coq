(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

let declare id entry =
  let _ : Constant.t =
    Declare.declare_constant ~name:id ~kind:Decls.IsPrimitive (Declare.PrimitiveEntry entry)
  in
  Flags.if_verbose Feedback.msg_info Pp.(Id.print id ++ str " is declared")

let do_primitive id udecl prim typopt =
  if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Declaring a primitive is not allowed in sections.");
  if Dumpglob.dump () then Dumpglob.dump_definition id false "ax";
  let loc = id.CAst.loc in
  let id = id.CAst.v in
  match typopt with
  | None ->
    if Option.has_some udecl then
      CErrors.user_err ?loc
        Pp.(strbrk "Cannot use a universe declaration without a type when declaring primitives.");
    let e = Declare.primitive_entry prim in
    declare id e
  | Some typ ->
    let env = Global.env () in
    let evd, udecl = Constrintern.interp_univ_decl_opt env udecl in
    let auctx = CPrimitives.op_or_type_univs prim in
    let evd, u = Evd.with_context_set UState.univ_flexible evd (UnivGen.fresh_instance auctx) in
    let expected_typ = EConstr.of_constr @@ Typeops.type_of_prim_or_type env u prim in
    let evd, (typ,impls) =
      Constrintern.(interp_type_evars_impls ~impls:empty_internalization_env)
        env evd typ
    in
    let evd = try Evarconv.unify_delay env evd typ expected_typ
      with Evarconv.UnableToUnify (evd,e) as exn ->
        let _, info = Exninfo.capture exn in
        Exninfo.iraise (Pretype_errors.(
            PretypeError (env,evd,CannotUnify (typ,expected_typ,Some e)),info))
    in
    Pretyping.check_evars_are_solved ~program_mode:false env evd;
    let evd = Evd.minimize_universes evd in
    let uvars = EConstr.universes_of_constr evd typ in
    let evd = Evd.restrict_universe_context evd uvars in
    let typ = EConstr.to_constr evd typ in
    let univ_entry = Evd.check_univ_decl ~poly:(not (Univ.AbstractContext.is_empty auctx)) evd udecl in
    let entry = Declare.primitive_entry ~types:(typ, univ_entry) prim in
    declare id entry
