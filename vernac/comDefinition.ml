(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Redexpr
open Constrintern
open Pretyping

(* Commands of the interface: Constant definitions *)

let red_constant_body red_opt env sigma body = match red_opt with
  | None -> sigma, body
  | Some red ->
    let red, _ = reduction_of_red_expr env red in
    red env sigma body

let warn_implicits_in_term =
  CWarnings.create ~name:"implicits-in-term" ~category:"implicits"
         (fun () ->
          strbrk "Implicit arguments declaration relies on type." ++ spc () ++
            strbrk "Discarding incompatible declaration in term.")

let check_imps ~impsty ~impsbody =
  let rec aux impsty impsbody =
  match impsty, impsbody with
  | a1 :: impsty, a2 :: impsbody ->
    (match a1.CAst.v, a2.CAst.v with
    | None , None -> aux impsty impsbody
    | Some _ , Some _ -> aux impsty impsbody
    | _, _ -> warn_implicits_in_term ?loc:a2.CAst.loc ())
  | _ :: _, [] | [], _ :: _ -> (* Information only on one side *) ()
  | [], [] -> () in
  aux impsty impsbody

let interp_definition ~program_mode pl bl ~poly red_option c ctypopt =
  let env = Global.env() in
  (* Explicitly bound universes and constraints *)
  let evd, udecl = Constrexpr_ops.interp_univ_decl_opt env pl in
  (* Build the parameters *)
  let evd, (impls, ((env_bl, ctx), imps1)) = interp_context_evars ~program_mode env evd bl in
  (* Build the type *)
  let evd, tyopt = Option.fold_left_map
      (interp_type_evars_impls ~program_mode ~impls env_bl)
      evd ctypopt
  in
  (* Build the body, and merge implicits from parameters and from type/body *)
  let evd, c, imps, tyopt =
    match tyopt with
    | None ->
      let evd, (c, impsbody) = interp_constr_evars_impls ~program_mode ~impls env_bl evd c in
      evd, c, imps1@impsbody, None
    | Some (ty, impsty) ->
      let evd, (c, impsbody) = interp_casted_constr_evars_impls ~program_mode ~impls env_bl evd c ty in
      check_imps ~impsty ~impsbody;
      evd, c, imps1@impsty, Some ty
  in
  (* Do the reduction *)
  let evd, c = red_constant_body red_option env_bl evd c in

  (* Declare the definition *)
  let c = EConstr.it_mkLambda_or_LetIn c ctx in
  let tyopt = Option.map (fun ty -> EConstr.it_mkProd_or_LetIn ty ctx) tyopt in

  let evd, ce = DeclareDef.prepare_definition ~allow_evars:program_mode
      ~opaque:false ~poly evd udecl ~types:tyopt ~body:c in

  (ce, evd, udecl, imps)

let check_definition ~program_mode (ce, evd, _, imps) =
  let env = Global.env () in
  check_evars_are_solved ~program_mode env evd;
  ce

let do_definition ~program_mode ?hook ~name ~scope ~poly ~kind univdecl bl red_option c ctypopt =
  let (ce, evd, univdecl, imps as def) =
    interp_definition ~program_mode univdecl bl ~poly red_option c ctypopt
  in
  if program_mode then
    let env = Global.env () in
    let (c,ctx), sideff = Future.force ce.Proof_global.proof_entry_body in
    assert(Safe_typing.empty_private_constants = sideff.Evd.seff_private);
    assert(Univ.ContextSet.is_empty ctx);
    Obligations.check_evars env evd;
    let c = EConstr.of_constr c in
    let typ = match ce.Proof_global.proof_entry_type with
      | Some t -> EConstr.of_constr t
      | None -> Retyping.get_type_of env evd c
    in
    let obls, _, c, cty =
      Obligations.eterm_obligations env name evd 0 c typ
    in
    let ctx = Evd.evar_universe_context evd in
    ignore(Obligations.add_definition
             ~name ~term:c cty ctx ~univdecl ~implicits:imps ~scope ~poly ~kind ?hook obls)
  else
    let ce = check_definition ~program_mode def in
    let uctx = Evd.evar_universe_context evd in
    let hook_data = Option.map (fun hook -> hook, uctx, []) hook in
    ignore(DeclareDef.declare_definition ~name ~scope ~kind ?hook_data (Evd.universe_binders evd) ce imps)
