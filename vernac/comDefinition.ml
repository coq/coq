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
open Util
open Entries
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
  let impsty = List.map (fun x -> x.CAst.v) impsty in
  List.iter (fun {CAst.v = (key, (va:bool*bool*bool)); CAst.loc} ->
      let b =
        try
          (* Pervasives.(=) is OK for this type *)
          Pervasives.(=) (List.assoc_f Constrexpr_ops.explicitation_eq key impsty) va
        with Not_found -> false
      in
      if not b then warn_implicits_in_term ?loc ())
    impsbody

let interp_definition ~program_mode pl bl poly red_option c ctypopt =
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
      evd, c, imps1@Impargs.lift_implicits (Context.Rel.nhyps ctx) impsbody, None
    | Some (ty, impsty) ->
      let evd, (c, impsbody) = interp_casted_constr_evars_impls ~program_mode ~impls env_bl evd c ty in
      check_imps ~impsty ~impsbody;
      evd, c, imps1@Impargs.lift_implicits (Context.Rel.nhyps ctx) impsty, Some ty
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

let do_definition ~program_mode ?hook ident k univdecl bl red_option c ctypopt =
  let (ce, evd, univdecl, imps as def) =
    interp_definition ~program_mode univdecl bl (pi2 k) red_option c ctypopt
  in
  if program_mode then
    let env = Global.env () in
    let (c,ctx), sideff = Future.force ce.const_entry_body in
    assert(Safe_typing.empty_private_constants = sideff.Evd.seff_private);
    assert(Univ.ContextSet.is_empty ctx);
    Obligations.check_evars env evd;
    let c = EConstr.of_constr c in
    let typ = match ce.const_entry_type with
      | Some t -> EConstr.of_constr t
      | None -> Retyping.get_type_of env evd c
    in
    let obls, _, c, cty =
      Obligations.eterm_obligations env ident evd 0 c typ
    in
    let ctx = Evd.evar_universe_context evd in
    ignore(Obligations.add_definition
             ident ~term:c cty ctx ~univdecl ~implicits:imps ~kind:k ?hook obls)
  else
    let ce = check_definition ~program_mode def in
    let uctx = Evd.evar_universe_context evd in
    let hook_data = Option.map (fun hook -> hook, uctx, []) hook in
    ignore(DeclareDef.declare_definition ident k ?hook_data ce (Evd.universe_binders evd) imps)
