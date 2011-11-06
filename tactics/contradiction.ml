(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Term
open Proof_type
open Hipattern
open Tacmach
open Tacticals
open Tactics
open Coqlib
open Reductionops
open Rawterm

(* Absurd *)

let absurd c gls =
  let env = pf_env gls and sigma = project gls in
  let _,j = Coercion.Default.inh_coerce_to_sort dummy_loc env
    (Evd.create_goal_evar_defs sigma) (Retyping.get_judgment_of env sigma c) in
  let c = j.Environ.utj_val in
  (tclTHENS
     (tclTHEN (elim_type (build_coq_False ())) (cut c))
     ([(tclTHENS
          (cut (applist(build_coq_not (),[c])))
	  ([(tclTHEN intros
	       ((fun gl ->
		   let ida = pf_nth_hyp_id gl 1
                   and idna = pf_nth_hyp_id gl 2 in
                   exact_no_check (applist(mkVar idna,[mkVar ida])) gl)));
            tclIDTAC]));
       tclIDTAC])) gls

(* Contradiction *)

let filter_hyp f tac gl =
  let rec seek = function
    | [] -> raise Not_found
    | (id,_,t)::rest when f t -> tac id gl
    | _::rest -> seek rest in
  seek (pf_hyps gl)

let contradiction_context gl =
  let env = pf_env gl in
  let sigma = project gl in
  let rec seek_neg l gl = match l with
    | [] ->  error "No such contradiction"
    | (id,_,typ)::rest ->
	let typ = whd_betadeltaiota env sigma typ in
	if is_empty_type typ then
	  simplest_elim (mkVar id) gl
	else match kind_of_term typ with
	  | Prod (na,t,u) when is_empty_type u ->
	      (try
		filter_hyp (fun typ -> pf_conv_x_leq gl typ t)
		  (fun id' -> simplest_elim (mkApp (mkVar id,[|mkVar id'|])))
		  gl
	      with Not_found -> seek_neg rest gl)
	  | _ -> seek_neg rest gl in
  seek_neg (pf_hyps gl) gl

let is_negation_of env sigma typ t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (na,t,u) -> is_empty_type u & is_conv_leq env sigma typ t
    | _ -> false

let contradiction_term (c,lbind as cl) gl =
  let env = pf_env gl in
  let sigma = project gl in
  let typ = pf_type_of gl c in
  let _, ccl = splay_prod env sigma typ in
  if is_empty_type ccl then
    tclTHEN (elim false cl None) (tclTRY assumption) gl
  else
    try
      if lbind = NoBindings then
	filter_hyp (is_negation_of env sigma typ)
	  (fun id -> simplest_elim (mkApp (mkVar id,[|c|]))) gl
      else
	raise Not_found
    with Not_found -> error "Not a contradiction."

let contradiction = function
  | None -> tclTHEN intros contradiction_context
  | Some c -> contradiction_term c
