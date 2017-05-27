(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Nameops
open CErrors
open Pp
open Vernacexpr

type universe_decl =
  (lident list, Univ.Constraint.t) gen_universe_decl

let default_univ_decl =
  let open Vernacexpr in
  { univdecl_instance = [];
    univdecl_extensible_instance = true;
    univdecl_constraints = Univ.Constraint.empty;
    univdecl_extensible_constraints = true }

let interp_univ_constraints env evd cstrs =
  let open Misctypes in
  let u_of_id x =
    match x with
    | Misctypes.GProp -> Loc.tag Univ.Level.prop
    | GSet  -> Loc.tag Univ.Level.set
    | GType None | GType (Some (_, Anonymous)) ->
       user_err ~hdr:"interp_constraint"
                     (str "Cannot declare constraints on anonymous universes")
    | GType (Some (loc, Name id)) ->
       try loc, Evd.universe_of_name evd (Id.to_string id) 
       with Not_found ->
         user_err ?loc ~hdr:"interp_constraint" (str "Undeclared universe " ++ pr_id id)
  in
  let interp (evd,cstrs) (u, d, u') =
    let lloc, ul = u_of_id u and rloc, u'l = u_of_id u' in
    let cstr = (ul,d,u'l) in
    let cstrs' = Univ.Constraint.add cstr cstrs in
    try let evd = Evd.add_constraints evd (Univ.Constraint.singleton cstr) in
        evd, cstrs'
    with Univ.UniverseInconsistency e ->
      user_err  ~hdr:"interp_constraint" (str "Universe inconsistency" (* TODO *))
  in
  List.fold_left interp (evd,Univ.Constraint.empty) cstrs

let interp_univ_decl env decl = 
  let pl = decl.univdecl_instance in
  let evd = Evd.from_ctx (Evd.make_evar_universe_context env (Some pl)) in
  let evd, cstrs = interp_univ_constraints env evd decl.univdecl_constraints in
  let decl = { univdecl_instance = pl;
    univdecl_extensible_instance = decl.univdecl_extensible_instance;
    univdecl_constraints = cstrs;
    univdecl_extensible_constraints = decl.univdecl_extensible_constraints }
  in evd, decl

let interp_univ_decl_opt env l =
  match l with
  | None -> Evd.from_env env, default_univ_decl
  | Some decl -> interp_univ_decl env decl

let check_implication evd cstrs ctx =
  let uctx = Evd.evar_universe_context evd in
  let gr = UState.initial_graph uctx in
  let grext = UGraph.merge_constraints cstrs gr in
  let cstrs' = Univ.UContext.constraints ctx in
  if UGraph.check_constraints cstrs' grext then ()
  else user_err ~hdr:"check_univ_decl"
                  (str "Universe constraints are not implied by the ones declared.")

let check_univ_decl evd decl = 
  let pl = if decl.univdecl_extensible_instance then None else Some decl.univdecl_instance in
  let pl, ctx = Evd.universe_context ?names:pl evd in
  if not decl.univdecl_extensible_constraints then
    check_implication evd decl.univdecl_constraints ctx;
  pl, ctx
              
