(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let do_primitive id prim typopt =
  if Global.sections_are_opened () then
    CErrors.user_err Pp.(str "Declaring a primitive is not allowed in sections.");
  if Dumpglob.dump () then Dumpglob.dump_definition id false "ax";
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, typopt = COption.fold_left_map
      Constrintern.(interp_type_evars_impls ~impls:empty_internalization_env env)
      evd typopt
  in
  let evd = Evd.minimize_universes evd in
  let uvars, impls, typopt = match typopt with
    | None -> Univ.LSet.empty, [], None
    | Some (ty,impls) ->
      EConstr.universes_of_constr evd ty, impls, Some (EConstr.to_constr evd ty)
  in
  let evd = Evd.restrict_universe_context evd uvars in
  let uctx = UState.check_mono_univ_decl (Evd.evar_universe_context evd) UState.default_univ_decl in
  let entry = Entries.{
      prim_entry_type = typopt;
      prim_entry_univs = uctx;
      prim_entry_content = prim;
    }
  in
  let _kn : Names.Constant.t =
    Declare.declare_constant ~name:id.CAst.v ~kind:Decls.IsPrimitive (Declare.PrimitiveEntry entry) in
  Flags.if_verbose Feedback.msg_info Pp.(Names.Id.print id.CAst.v ++ str " is declared")
