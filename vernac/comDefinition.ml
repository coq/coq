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
open Constr
open Environ
open Entries
open Redexpr
open Declare
open Constrintern
open Pretyping

open Context.Rel.Declaration

(* Commands of the interface: Constant definitions *)

let rec under_binders env sigma f n c =
  if Int.equal n 0 then f env sigma (EConstr.of_constr c) else
    match Constr.kind c with
      | Lambda (x,t,c) ->
          mkLambda (x,t,under_binders (push_rel (LocalAssum (x,t)) env) sigma f (n-1) c)
      | LetIn (x,b,t,c) ->
          mkLetIn (x,b,t,under_binders (push_rel (LocalDef (x,b,t)) env) sigma f (n-1) c)
      | _ -> assert false

let red_constant_entry n ce sigma = function
  | None -> ce
  | Some red ->
      let proof_out = ce.const_entry_body in
      let env = Global.env () in
      let (redfun, _) = reduction_of_red_expr env red in
      let redfun env sigma c =
        let (_, c) = redfun env sigma c in
        EConstr.Unsafe.to_constr c
      in
      { ce with const_entry_body = Future.chain proof_out
        (fun ((body,ctx),eff) -> (under_binders env sigma redfun n body,ctx),eff) }

let warn_implicits_in_term =
  CWarnings.create ~name:"implicits-in-term" ~category:"implicits"
         (fun () ->
          strbrk "Implicit arguments declaration relies on type." ++ spc () ++
            strbrk "The term declares more implicits than the type here.")

let check_imps ~impsty ~impsbody =
  let b =
    try
      List.for_all (fun (key, (va:bool*bool*bool)) ->
          (* Pervasives.(=) is OK for this type *)
          Pervasives.(=) (List.assoc_f Impargs.explicitation_eq key impsty) va)
        impsbody
    with Not_found -> false
  in
  if not b then warn_implicits_in_term ()

let interp_definition pl bl poly red_option c ctypopt =
  let open EConstr in
  let env = Global.env() in
  (* Explicitly bound universes and constraints *)
  let evd, decl = Univdecls.interp_univ_decl_opt env pl in
  (* Build the parameters *)
  let evd, (impls, ((env_bl, ctx), imps1)) = interp_context_evars env evd bl in
  (* Build the type *)
  let evd, tyopt = Option.fold_left_map
      (interp_type_evars_impls ~impls env_bl)
      evd ctypopt
  in
  (* Build the body, and merge implicits from parameters and from type/body *)
  let evd, c, imps, tyopt =
    match tyopt with
    | None ->
      let evd, (c, impsbody) = interp_constr_evars_impls ~impls env_bl evd c in
      evd, c, imps1@Impargs.lift_implicits (Context.Rel.nhyps ctx) impsbody, None
    | Some (ty, impsty) ->
      let evd, (c, impsbody) = interp_casted_constr_evars_impls ~impls env_bl evd c ty in
      check_imps ~impsty ~impsbody;
      evd, c, imps1@Impargs.lift_implicits (Context.Rel.nhyps ctx) impsty, Some ty
  in
  (* universe minimization *)
  let evd = Evd.minimize_universes evd in
  (* Substitute evars and universes, and add parameters.
     Note: in program mode some evars may remain. *)
  let ctx = List.map (EConstr.to_rel_decl evd) ctx in
  let c = Term.it_mkLambda_or_LetIn (EConstr.to_constr evd c) ctx in
  let tyopt = Option.map (fun ty -> Term.it_mkProd_or_LetIn (EConstr.to_constr evd ty) ctx) tyopt in
  (* Keep only useful universes. *)
  let uvars_fold uvars c =
    Univ.LSet.union uvars (universes_of_constr env evd (of_constr c))
  in
  let uvars = List.fold_left uvars_fold Univ.LSet.empty (Option.List.cons tyopt [c]) in
  let evd = Evd.restrict_universe_context evd uvars in
  (* Check we conform to declared universes *)
  let uctx = Evd.check_univ_decl ~poly evd decl in
  (* We're done! *)
  let ce = definition_entry ?types:tyopt ~univs:uctx c in
  (red_constant_entry (Context.Rel.length ctx) ce evd red_option, evd, decl, imps)

let check_definition (ce, evd, _, imps) =
  check_evars_are_solved (Global.env ()) evd Evd.empty;
  ce

let do_definition ~program_mode ident k univdecl bl red_option c ctypopt hook =
  let (ce, evd, univdecl, imps as def) =
    interp_definition univdecl bl (pi2 k) red_option c ctypopt
  in
    if program_mode then
      let env = Global.env () in
      let (c,ctx), sideff = Future.force ce.const_entry_body in
      assert(Safe_typing.empty_private_constants = sideff);
      assert(Univ.ContextSet.is_empty ctx);
      let typ = match ce.const_entry_type with
        | Some t -> t
        | None -> EConstr.to_constr evd (Retyping.get_type_of env evd (EConstr.of_constr c))
      in
      Obligations.check_evars env evd;
      let obls, _, c, cty =
        Obligations.eterm_obligations env ident evd 0 c typ
      in
      let ctx = Evd.evar_universe_context evd in
      let hook = Lemmas.mk_hook (fun l r _ -> Lemmas.call_hook (fun exn -> exn) hook l r) in
      ignore(Obligations.add_definition
          ident ~term:c cty ctx ~univdecl ~implicits:imps ~kind:k ~hook obls)
    else let ce = check_definition def in
      ignore(DeclareDef.declare_definition ident k ce (Evd.universe_binders evd) imps
        (Lemmas.mk_hook
          (fun l r -> Lemmas.call_hook (fun exn -> exn) hook l r;r)))
