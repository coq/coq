(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

(* Absurd *)

let absurd c gls =
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

let contradiction = tclTHEN intros contradiction_context

let is_negation_of env sigma typ t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (na,t,u) -> is_empty_type u & is_conv_leq env sigma typ t
    | _ -> false

let contradiction_term c gl =
  let env = pf_env gl in
  let sigma = project gl in
  let typ = pf_type_of gl c in
  if is_empty_type typ then
    simplest_elim c gl
  else
    try
      (match kind_of_term (whd_betadeltaiota env sigma typ) with
	| Prod (na,t,u) when is_empty_type u ->
	    filter_hyp (fun typ -> pf_conv_x_leq gl typ t)
	    (fun id -> simplest_elim (mkApp (c,[|mkVar id|]))) gl
	| _ ->
	    filter_hyp (is_negation_of env sigma typ)
	    (fun id -> simplest_elim (mkApp (mkVar id,[|c|]))) gl)
    with Not_found -> error "Not a contradiction"
