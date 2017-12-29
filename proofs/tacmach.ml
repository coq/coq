(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Namegen
open Termops
open Environ
open Reductionops
open Evd
open Typing
open Redexpr
open Tacred
open Proof_type
open Logic
open Refiner
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

let re_sig it  gc = { it = it; sigma = gc; }

(**************************************************************)
(* Operations for handling terms under a local typing context *)
(**************************************************************)

type 'a sigma   = 'a Evd.sigma;;
type tactic     = Proof_type.tactic;;

[@@@ocaml.warning "-3"]
let unpackage = Refiner.unpackage
let repackage = Refiner.repackage
let apply_sig_tac = Refiner.apply_sig_tac
[@@@ocaml.warning "+3"]

let sig_it   = Refiner.sig_it
let project  = Refiner.project
let pf_env   = Refiner.pf_env
let pf_hyps  = Refiner.pf_hyps

let test_conversion env sigma pb c1 c2 =
  Reductionops.check_conv ~pb env sigma c1 c2

let pf_concl gls = Goal.V82.concl (project gls) (sig_it gls)
let pf_hyps_types gls  =
  let sign = Environ.named_context (pf_env gls) in
  List.map (function LocalAssum (id,x)
                   | LocalDef (id,_,x) -> id, EConstr.of_constr x)
           sign

let pf_nth_hyp_id gls n = List.nth (pf_hyps gls) (n-1) |> NamedDecl.get_id

let pf_last_hyp gl = List.hd (pf_hyps gl)

let pf_get_hyp gls id =
  let env, sigma = pf_env gls, project gls in
  try
    Context.Named.lookup id (pf_hyps gls)
  with Not_found ->
    raise (RefinerError (env, sigma, NoSuchHyp id))

let pf_get_hyp_typ gls id =
  id |> pf_get_hyp gls |> NamedDecl.get_type

let pf_ids_of_hyps gls = ids_of_named_context (pf_hyps gls)
let pf_ids_set_of_hyps gls =
  Environ.ids_of_named_context_val (Environ.named_context_val (pf_env gls))

let pf_get_new_id id gls =
  next_ident_away id (pf_ids_set_of_hyps gls)

let pf_global gls id = EConstr.of_constr (UnivGen.constr_of_global (Constrintern.construct_reference (pf_hyps gls) id))

let pf_reduction_of_red_expr gls re c =
  let (redfun, _) = reduction_of_red_expr (pf_env gls) re in
  let sigma = project gls in
  redfun (pf_env gls) sigma c

let pf_apply f gls = f (pf_env gls) (project gls)
let pf_eapply f gls x = 
  on_sig gls (fun evm -> f (pf_env gls) evm x)
let pf_reduce = pf_apply
let pf_e_reduce = pf_apply

let pf_whd_all         = pf_reduce whd_all
let pf_hnf_constr                = pf_reduce hnf_constr
let pf_nf                        = pf_reduce simpl
let pf_nf_betaiota               = pf_reduce nf_betaiota
let pf_compute                   = pf_reduce compute
let pf_unfoldn ubinds            = pf_reduce (unfoldn ubinds)
let pf_unsafe_type_of            = pf_reduce unsafe_type_of
let pf_type_of                   = pf_reduce type_of
let pf_get_type_of               = pf_reduce Retyping.get_type_of

let pf_conv_x gl                = pf_reduce test_conversion gl Reduction.CONV
let pf_conv_x_leq gl            = pf_reduce test_conversion gl Reduction.CUMUL
let pf_const_value              = pf_reduce (fun env _ c -> EConstr.of_constr (constant_value_in env c))

let pf_reduce_to_quantified_ind = pf_reduce reduce_to_quantified_ind
let pf_reduce_to_atomic_ind     = pf_reduce reduce_to_atomic_ind

let pf_hnf_type_of gls          = pf_get_type_of gls %> pf_whd_all gls

(********************************************)
(* Definition of the most primitive tactics *)
(********************************************)

let refiner = refiner

let refine_no_check c gl =
  let c = EConstr.Unsafe.to_constr c in
  refiner (Refine c) gl

(* Versions with consistency checks *)

let refine c           = with_check (refine_no_check c)

(* Pretty-printers *)

open Pp

let db_pr_goal sigma g =
  let env = Goal.V82.env sigma g in
  let penv = Termops.Internal.print_named_context env in
  let pc = Termops.Internal.print_constr_env env sigma (Goal.V82.concl sigma g) in
  str"  " ++ hv 0 (penv ++ fnl () ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

let pr_gls gls =
  hov 0 (pr_evar_map (Some 2) (sig_sig gls) ++ fnl () ++ db_pr_goal (project gls) (sig_it gls))

let pr_glls glls =
  hov 0 (pr_evar_map (Some 2) (sig_sig glls) ++ fnl () ++
         prlist_with_sep fnl (db_pr_goal (project glls)) (sig_it glls))

(* Variants of [Tacmach] functions built with the new proof engine *)
module New = struct

  let project gl =
    Proofview.Goal.sigma gl

  let pf_apply f gl =
    f (Proofview.Goal.env gl) (project gl)

  let of_old f gl =
    f { Evd.it = Proofview.Goal.goal gl ; sigma = project gl; }

  let pf_global id gl =
    (** We only check for the existence of an [id] in [hyps] *)
    let hyps = Proofview.Goal.hyps gl in
    Constrintern.construct_reference hyps id

  let pf_env = Proofview.Goal.env
  let pf_concl = Proofview.Goal.concl

  let pf_unsafe_type_of gl t =
    pf_apply unsafe_type_of gl t

  let pf_type_of gl t =
    pf_apply type_of gl t

  let pf_conv_x gl t1 t2 = pf_apply is_conv gl t1 t2

  let pf_ids_of_hyps gl =
    (** We only get the identifiers in [hyps] *)
    let hyps = Proofview.Goal.hyps gl in
    ids_of_named_context hyps

  let pf_ids_set_of_hyps gl =
    (** We only get the identifiers in [hyps] *)
    let env = Proofview.Goal.env gl in
    Environ.ids_of_named_context_val (Environ.named_context_val env)

  let pf_get_new_id id gl =
    let ids = pf_ids_set_of_hyps gl in
    next_ident_away id ids

  let pf_get_hyp id gl =
    let hyps = Proofview.Goal.env gl in
    let sigma = project gl in
    let sign =
      try EConstr.lookup_named id hyps
      with Not_found -> raise (RefinerError (hyps, sigma, NoSuchHyp id))
    in
    sign

  let pf_get_hyp_typ id gl =
    pf_get_hyp id gl |> NamedDecl.get_type

  let pf_hyps_types gl =
    let env = Proofview.Goal.env gl in
    let sign = Environ.named_context env in
    List.map (function LocalAssum (id,x)
                     | LocalDef (id,_,x) -> id, EConstr.of_constr x)
             sign

  let pf_last_hyp gl =
    let hyps = Proofview.Goal.hyps gl in
    List.hd hyps

  let pf_nf_concl (gl : Proofview.Goal.t) =
    (** We normalize the conclusion just after *)
    let concl = Proofview.Goal.concl gl in
    let sigma = project gl in
    nf_evar sigma concl

  let pf_whd_all gl t = pf_apply whd_all gl t

  let pf_get_type_of gl t = pf_apply Retyping.get_type_of gl t

  let pf_reduce_to_quantified_ind gl t =
    pf_apply reduce_to_quantified_ind gl t

  let pf_hnf_constr gl t = pf_apply hnf_constr gl t
  let pf_hnf_type_of gl t =
    pf_whd_all gl (pf_get_type_of gl t)

  let pf_whd_all gl t = pf_apply whd_all gl t
  let pf_compute gl t = pf_apply compute gl t

  let pf_nf_evar gl t = nf_evar (project gl) t

end
