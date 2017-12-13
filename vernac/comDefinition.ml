(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2018     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Constr
open Environ
open Entries
open Termops
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

let interp_definition pl bl poly red_option c ctypopt =
  let env = Global.env() in
  let evd, decl = Univdecls.interp_univ_decl_opt env pl in
  let evd, (impls, ((env_bl, ctx), imps1)) = interp_context_evars env evd bl in
  let ctx = List.map (fun d -> map_rel_decl EConstr.Unsafe.to_constr d) ctx in
  let nb_args = Context.Rel.nhyps ctx in
  let evd,imps,ce =
    match ctypopt with
      None ->
        let evd, subst = Evd.nf_univ_variables evd in
        let ctx = Context.Rel.map (Vars.subst_univs_constr subst) ctx in
        let env_bl = push_rel_context ctx env in
        let evd, (c, imps2) = interp_constr_evars_impls ~impls env_bl evd c in
        let c = EConstr.Unsafe.to_constr c in
        let evd,nf = Evarutil.nf_evars_and_universes evd in
        let body = nf (it_mkLambda_or_LetIn c ctx) in
        let vars = EConstr.universes_of_constr env evd (EConstr.of_constr body) in
        let evd = Evd.restrict_universe_context evd vars in
        let uctx = Evd.check_univ_decl ~poly evd decl in
        evd, imps1@(Impargs.lift_implicits nb_args imps2),
          definition_entry ~univs:uctx body
    | Some ctyp ->
        let evd, (ty, impsty) = interp_type_evars_impls ~impls env_bl evd ctyp in
        let evd, subst = Evd.nf_univ_variables evd in
        let ctx = Context.Rel.map (Vars.subst_univs_constr subst) ctx in
        let env_bl = push_rel_context ctx env in
        let evd, (c, imps2) = interp_casted_constr_evars_impls ~impls env_bl evd c ty in
        let c = EConstr.Unsafe.to_constr c in
        let evd, nf = Evarutil.nf_evars_and_universes evd in
        let body = nf (it_mkLambda_or_LetIn c ctx) in
        let ty = EConstr.Unsafe.to_constr ty in
        let typ = nf (Term.it_mkProd_or_LetIn ty ctx) in
        let beq b1 b2 = if b1 then b2 else not b2 in
        let impl_eq (x,y,z) (x',y',z') = beq x x' && beq y y' && beq z z' in
        (* Check that all implicit arguments inferable from the term
           are inferable from the type *)
        let chk (key,va) =
          impl_eq (List.assoc_f Pervasives.(=) key impsty) va (* FIXME *)
        in
        if not (try List.for_all chk imps2 with Not_found -> false)
        then warn_implicits_in_term ();
        let bodyvars = EConstr.universes_of_constr env evd (EConstr.of_constr body) in
        let tyvars = EConstr.universes_of_constr env evd (EConstr.of_constr ty) in
        let vars = Univ.LSet.union bodyvars tyvars in
        let evd = Evd.restrict_universe_context evd vars in
        let uctx = Evd.check_univ_decl ~poly evd decl in
        evd, imps1@(Impargs.lift_implicits nb_args impsty),
          definition_entry ~types:typ ~univs:uctx body
  in
  (red_constant_entry (Context.Rel.length ctx) ce evd red_option, evd, decl, imps)

let check_definition (ce, evd, _, imps) =
  check_evars_are_solved (Global.env ()) evd Evd.empty;
  ce

let do_definition ident k univdecl bl red_option c ctypopt hook =
  let (ce, evd, univdecl, imps as def) =
    interp_definition univdecl bl (pi2 k) red_option c ctypopt
  in
    if Flags.is_program_mode () then
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
