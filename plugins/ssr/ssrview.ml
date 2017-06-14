(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is (C) Copyright 2006-2015 Microsoft Corporation and Inria. *)

open Util
open Names
open Term
open Ltac_plugin
open Tacinterp
open Glob_term
open Tacmach
open Tacticals

open Ssrcommon

(* The table and its display command *)

(* FIXME this looks hackish *)

let viewtab : glob_constr list array = Array.make 3 []

let _ =
  let init () = Array.fill viewtab 0 3 [] in
  let freeze _ = Array.copy viewtab in
  let unfreeze vt = Array.blit vt 0 viewtab 0 3 in
  Summary.declare_summary "ssrview"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init }

(* Populating the table *)

let cache_viewhint (_, (i, lvh)) =
  let mem_raw h = List.exists (Glob_ops.glob_constr_eq h) in
  let add_hint h hdb = if mem_raw h hdb then hdb else h :: hdb in
  viewtab.(i) <- List.fold_right add_hint lvh viewtab.(i)

let subst_viewhint ( subst, (i, lvh as ilvh)) =
  let lvh' = List.smartmap (Detyping.subst_glob_constr subst) lvh in
  if lvh' == lvh then ilvh else i, lvh'
      
let classify_viewhint x = Libobject.Substitute x

let in_viewhint =
  Libobject.declare_object {(Libobject.default_object "VIEW_HINTS") with
       Libobject.open_function = (fun i o -> if i = 1 then cache_viewhint o);
       Libobject.cache_function = cache_viewhint;
       Libobject.subst_function = subst_viewhint;
       Libobject.classify_function = classify_viewhint }

let glob_view_hints lvh =
  List.map (Constrintern.intern_constr (Global.env ())) lvh

let add_view_hints lvh i = Lib.add_anonymous_leaf (in_viewhint (i, lvh))

let interp_view ist si env sigma gv v rid =
  let open CAst in
  match v with
  | { v = GApp ( { v = GHole _ } , rargs); loc } ->
    let rv = make ?loc @@ GApp (rid, rargs) in
    snd (interp_open_constr ist (re_sig si sigma) (rv, None))
  | rv ->
  let interp rc rargs =
    interp_open_constr ist (re_sig si sigma) (mkRApp rc rargs, None) in
  let rec simple_view rargs n =
    if n < 0 then view_error "use" gv else
    try interp rv rargs with _ -> simple_view (mkRHole :: rargs) (n - 1) in
  let view_nbimps = interp_view_nbimps ist (re_sig si sigma) rv in
  let view_args = [mkRApp rv (mkRHoles view_nbimps); rid] in
  let rec view_with = function
  | [] -> simple_view [rid] (interp_nbargs ist (re_sig si sigma) rv)
  | hint :: hints -> try interp hint view_args with _ -> view_with hints in
  snd (view_with (if view_nbimps < 0 then [] else viewtab.(0)))


let with_view ist ~next si env (gl0 : (Goal.goal * tac_ctx) Evd.sigma) c name cl prune (conclude : EConstr.t -> EConstr.t -> tac_ctx tac_a) clr =
  let c2r ist x = { ist with lfun =
    Id.Map.add top_id (Value.of_constr x) ist.lfun } in
  let terminate (sigma, c') =
    let sigma = Typeclasses.resolve_typeclasses ~fail:false env sigma in
    let c' = Reductionops.nf_evar sigma c' in
    let n, c', _, ucst = without_ctx pf_abs_evars gl0 (sigma, c') in
    let c' = if not prune then c' else without_ctx pf_abs_cterm gl0 n c' in
    let gl0 = pf_merge_uc ucst gl0 in
    let gl0, ap =
      let gl0, ctx = pull_ctx gl0 in
      let gl0, ap = pf_abs_prod name gl0 c' (Termops.prod_applist sigma cl [c]) in
      push_ctx ctx gl0, ap in
    let gl0 = pf_merge_uc_of sigma gl0 in
    ap, c', gl0 in
  let rec loop (sigma, c') = function
  | [] ->
      let ap, c', gl = terminate (sigma, c') in
      ap, c', conclude ap c' gl
  | f :: view ->
      let ist, rid =
        match EConstr.kind sigma c' with
        | Var id -> ist,mkRVar id
        | _ -> c2r ist c',mkRltacVar top_id in
      let v = intern_term ist env f in
      loop (interp_view ist si env sigma f v rid) view
  in loop

let pfa_with_view ist ?(next=ref []) (prune, view) cl c conclude clr gl =
  let env, sigma, si =
    without_ctx pf_env gl, Refiner.project gl, without_ctx sig_it gl in
  with_view
    ist ~next si env gl c (constr_name sigma c) cl prune conclude clr (sigma, c) view 

let pf_with_view_linear ist gl v cl c =
  let x,y,gl =
    pfa_with_view ist v cl c (fun _ _ -> tac_ctx tclIDTAC) []
      (push_ctx (new_ctx ()) gl) in
  let gl, _ = pull_ctxs gl in
  assert(List.length (sig_it gl) = 1);
  x,y,re_sig (List.hd (sig_it gl)) (Refiner.project gl)


(* vim: set filetype=ocaml foldmethod=marker: *)
