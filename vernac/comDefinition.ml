(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Redexpr
open Constrintern

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
      let () = match a1.CAst.v, a2.CAst.v with
        | None , None | Some _, None -> ()
        | Some (_,b1) , Some (_,b2) ->
          if not ((b1:bool) = b2) then warn_implicits_in_term ?loc:a2.CAst.loc ()
        | None, Some _ -> warn_implicits_in_term ?loc:a2.CAst.loc ()
      in
      aux impsty impsbody
    | _ :: _, [] | [], _ :: _ -> (* Information only on one side *) ()
    | [], [] -> () in
  aux impsty impsbody

let protect_pattern_in_binder bl c ctypopt =
  (* We turn "Definition d binders := body : typ" into *)
  (* "Definition d := fun binders => body:type" *)
  (* This is a hack while waiting for LocalPattern in regular environments *)
  if List.exists (function Constrexpr.CLocalPattern _ -> true | _ -> false) bl
  then
    let t = match ctypopt with
      | None -> CAst.make ?loc:c.CAst.loc (Constrexpr.CHole (None,Namegen.IntroAnonymous,None))
      | Some t -> t in
    let loc = Loc.merge_opt c.CAst.loc t.CAst.loc in
    let c = CAst.make ?loc @@ Constrexpr.CCast (c, Constr.DEFAULTcast, t) in
    let loc = match List.hd bl with
      | Constrexpr.CLocalAssum (a::_,_,_) | Constrexpr.CLocalDef (a,_,_) -> a.CAst.loc
      | Constrexpr.CLocalPattern {CAst.loc} -> loc
      | Constrexpr.CLocalAssum ([],_,_) -> assert false in
    let apply_under_binders f env evd c =
      let rec aux env evd c =
        let open Constr in
        let open EConstr in
        let open Context.Rel.Declaration in
        match kind evd c with
        | Lambda (x,t,c)  ->
          let evd,c = aux (push_rel (LocalAssum (x,t)) env) evd c in
          evd, mkLambda (x,t,c)
        | LetIn (x,b,t,c) ->
          let evd,c = aux (push_rel (LocalDef (x,b,t)) env) evd c in
          evd, mkLetIn (x,t,b,c)
        | Case (ci,u,pms,p,iv,a,bl) ->
          let (ci, p, iv, a, bl) = EConstr.expand_case env evd (ci, u, pms, p, iv, a, bl) in
          let evd,bl = Array.fold_left_map (aux env) evd bl in
          evd, mkCase (EConstr.contract_case env evd (ci, p, iv, a, bl))
        | Cast (c,_,_)    -> f env evd c  (* we remove the cast we had set *)
        (* This last case may happen when reaching the proof of an
           impossible case, as when pattern-matching on a vector of length 1 *)
        | _ -> (evd,c) in
      aux env evd c in
    ([], Constrexpr_ops.mkLambdaCN ?loc:(Loc.merge_opt loc c.CAst.loc) bl c, None, apply_under_binders)
  else
    (bl, c, ctypopt, fun f env evd c -> f env evd c)

let interp_definition ~program_mode env evd impl_env bl red_option c ctypopt =
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let (bl, c, ctypopt, apply_under_binders) = protect_pattern_in_binder bl c ctypopt in
  (* Build the parameters *)
  let evd, (impls, ((env_bl, ctx), imps1)) = interp_context_evars ~program_mode ~impl_env env evd bl in
  (* Build the type *)
  let evd, tyopt = Option.fold_left_map
      (interp_type_evars_impls ~flags ~impls env_bl)
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
  let evd, c = apply_under_binders (red_constant_body red_option) env_bl evd c in

  (* Declare the definition *)
  let c = EConstr.it_mkLambda_or_LetIn c ctx in
  let tyopt = Option.map (fun ty -> EConstr.it_mkProd_or_LetIn ty ctx) tyopt in
  evd, (c, tyopt), imps

let definition_using env evd ~body ~types ~using =
  let terms = Option.List.cons types [body] in
  Option.map (fun using -> Proof_using.definition_using env evd ~using ~terms) using

let do_definition ?hook ~name ?scope ~poly ?typing_flags ~kind ?using udecl bl red_option c ctypopt =
  let program_mode = false in
  let env = Global.env() in
  let env = Environ.update_typing_flags ?typing_flags env in
  (* Explicitly bound universes and constraints *)
  let evd, udecl = interp_univ_decl_opt env udecl in
  let evd, (body, types), impargs =
    interp_definition ~program_mode env evd empty_internalization_env bl red_option c ctypopt
  in
  let using = definition_using env evd ~body ~types ~using in
  let kind = Decls.IsDefinition kind in
  let cinfo = Declare.CInfo.make ~name ~impargs ~typ:types ?using () in
  let info = Declare.Info.make ?scope ~kind ?hook ~udecl ~poly ?typing_flags () in
  let _ : Names.GlobRef.t =
    Declare.declare_definition ~info ~cinfo ~opaque:false ~body evd
  in ()

let do_definition_program ?hook ~pm ~name ~scope ~poly ?typing_flags ~kind ?using udecl bl red_option c ctypopt =
  let () = if not poly then udecl |> Option.iter (fun udecl ->
      if not udecl.UState.univdecl_extensible_instance
      || not udecl.UState.univdecl_extensible_constraints
      then
        CErrors.user_err
          Pp.(str "Non extensible universe declaration not supported \
                   with monomorphic Program Definition."))
  in
  let env = Global.env() in
  let env = Environ.update_typing_flags ?typing_flags env in
  (* Explicitly bound universes and constraints *)
  let evd, udecl = interp_univ_decl_opt env udecl in
  let evd, (body, types), impargs =
    interp_definition ~program_mode:true env evd empty_internalization_env bl red_option c ctypopt
  in
  let using = definition_using env evd ~body ~types ~using in
  let term, typ, uctx, obls = Declare.Obls.prepare_obligation ~name ~body ~types evd in
  let pm, _ =
    let cinfo = Declare.CInfo.make ~name ~typ ~impargs ?using () in
    let info = Declare.Info.make ~udecl ~scope ~poly ~kind ?hook ?typing_flags () in
    Declare.Obls.add_definition ~pm ~cinfo ~info ~term ~uctx obls
  in pm
