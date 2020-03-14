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
  (c, tyopt), evd, udecl, imps

let do_definition ?hook ~name ~scope ~poly ~kind udecl bl red_option c ctypopt =
  let program_mode = false in
  let (body, types), evd, udecl, impargs =
    interp_definition ~program_mode udecl bl ~poly red_option c ctypopt
  in
  let evd, ce = DeclareDef.prepare_definition ~opaque:false ~poly evd ~udecl ~types ~body in
  let uctx = Evd.evar_universe_context evd in
  let hook_data = Option.map (fun hook -> hook, uctx, []) hook in
  let kind = Decls.IsDefinition kind in
  let ubind = Evd.universe_binders evd in
  let _ : Names.GlobRef.t =
    DeclareDef.declare_definition ~name ~scope ~kind ?hook_data ~ubind ~impargs ce
  in ()

let do_definition_program ?hook ~name ~scope ~poly ~kind udecl bl red_option c ctypopt =
  let program_mode = true in
  let (body, types), evd, udecl, impargs =
    interp_definition ~program_mode udecl bl ~poly red_option c ctypopt
  in
  let term, ty, uctx, obls = DeclareDef.prepare_obligation ~name ~poly ~body ~types ~udecl evd in
  let _ : DeclareObl.progress =
    Obligations.add_definition
      ~name ~term ty ~uctx ~udecl ~impargs ~scope ~poly ~kind ?hook obls
  in ()
