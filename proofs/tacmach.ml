(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Namegen
open Termops
open Reductionops
open Typing
open Tacred
open Logic
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

(* Variants of [Tacmach] functions built with the new proof engine *)

let project gl =
  Proofview.Goal.sigma gl

let pf_apply f gl =
  f (Proofview.Goal.env gl) (project gl)

let pf_env = Proofview.Goal.env
let pf_concl = Proofview.Goal.concl

let pf_type_of gl t =
  pf_apply type_of gl t

let pf_conv_x gl t1 t2 = pf_apply is_conv gl t1 t2

let pf_ids_of_hyps gl =
  (* We only get the identifiers in [hyps] *)
  let hyps = Proofview.Goal.hyps gl in
  ids_of_named_context hyps

let pf_ids_set_of_hyps gl =
  (* We only get the identifiers in [hyps] *)
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
                    | LocalDef (id,_,x) -> id.Context.binder_name, EConstr.of_constr x)
            sign

let pf_last_hyp gl =
  let hyps = Proofview.Goal.hyps gl in
  List.hd hyps

let pf_nf_concl (gl : Proofview.Goal.t) =
  (* We normalize the conclusion just after *)
  let concl = Proofview.Goal.concl gl in
  let sigma = project gl in
  nf_evar sigma concl

let pf_whd_all gl t = pf_apply whd_all gl t

let pf_get_type_of gl t = pf_apply Retyping.get_type_of gl t

let pf_hnf_constr gl t = pf_apply hnf_constr gl t
let pf_hnf_type_of gl t =
  pf_whd_all gl (pf_get_type_of gl t)

let pf_compute gl t = pf_apply compute gl t
let pf_whd_compute gl t = pf_apply whd_compute gl t

let pf_nf_evar gl t = nf_evar (project gl) t

open Pp

let pr_gls gl =
  let sigma = project gl in
  let env = pf_env gl in
  let concl = Proofview.Goal.concl gl in
  let penv = Termops.Internal.print_named_context env sigma in
  let pc = Termops.Internal.print_constr_env env sigma concl in
  let g = str"  " ++ hv 0 (penv ++ fnl () ++
                  str "============================" ++ fnl ()  ++
                  str" "  ++ pc) ++ fnl ()
  in
  hov 0 (pr_evar_map (Some 2) env sigma ++ fnl () ++ g)
