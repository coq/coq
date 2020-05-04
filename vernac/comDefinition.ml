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
    (match a1.CAst.v, a2.CAst.v with
    | None , None -> aux impsty impsbody
    | Some _ , Some _ -> aux impsty impsbody
    | _, _ -> warn_implicits_in_term ?loc:a2.CAst.loc ())
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
    let c = CAst.make ?loc @@ Constrexpr.CCast (c, Glob_term.CastConv t) in
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
        | Case (ci,p,a,bl) ->
          let evd,bl = Array.fold_left_map (aux env) evd bl in
          evd, mkCase (ci,p,a,bl)
        | Cast (c,_,_)    -> f env evd c  (* we remove the cast we had set *)
        (* This last case may happen when reaching the proof of an
           impossible case, as when pattern-matching on a vector of length 1 *)
        | _ -> (evd,c) in
      aux env evd c in
    ([], Constrexpr_ops.mkLambdaCN ?loc:(Loc.merge_opt loc c.CAst.loc) bl c, None, apply_under_binders)
  else
    (bl, c, ctypopt, fun f env evd c -> f env evd c)

let interp_definition ~program_mode pl bl ~poly red_option c ctypopt =
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let env = Global.env() in
  (* Explicitly bound universes and constraints *)
  let evd, udecl = Constrexpr_ops.interp_univ_decl_opt env pl in
  let (bl, c, ctypopt, apply_under_binders) = protect_pattern_in_binder bl c ctypopt in
  (* Build the parameters *)
  let evd, (impls, ((env_bl, ctx), imps1)) = interp_context_evars ~program_mode env evd bl in
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
  (c, tyopt), evd, udecl, imps

let do_definition ?hook ~name ~scope ~poly ~kind udecl bl red_option c ctypopt =
  let program_mode = false in
  let (body, types), evd, udecl, impargs =
    interp_definition ~program_mode udecl bl ~poly red_option c ctypopt
  in
  let kind = Decls.IsDefinition kind in
  let _ : Names.GlobRef.t =
    Declare.declare_definition ~name ~scope ~kind ?hook ~impargs
      ~opaque:false ~poly evd ~udecl ~types ~body
  in ()

let do_definition_program ?hook ~name ~scope ~poly ~kind udecl bl red_option c ctypopt =
  let program_mode = true in
  let (body, types), evd, udecl, impargs =
    interp_definition ~program_mode udecl bl ~poly red_option c ctypopt
  in
  let term, ty, uctx, obls = Declare.prepare_obligation ~name ~poly ~body ~types ~udecl evd in
  let _ : Declare.Obls.progress =
    Obligations.add_definition
      ~name ~term ty ~uctx ~udecl ~impargs ~scope ~poly ~kind ?hook obls
  in ()
