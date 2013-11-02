(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Term
open Hipattern
open Tacmach
open Tacticals
open Tactics
open Coqlib
open Reductionops
open Misctypes
open Proofview.Notations

(* Absurd *)

let absurd c gls =
  let env = pf_env gls and sigma = project gls in
  let j = Retyping.get_judgment_of env sigma c in
  let sigma, j = Coercion.inh_coerce_to_sort Loc.ghost env sigma j in
  let c = j.Environ.utj_val in
  (tclTHENS
     (tclTHEN (elim_type (build_coq_False ())) (cut c))
     ([(tclTHENS
          (cut (mkApp(build_coq_not (),[|c|])))
	  ([(tclTHEN (Proofview.V82.of_tactic intros)
	       ((fun gl ->
		   let ida = pf_nth_hyp_id gl 1
                   and idna = pf_nth_hyp_id gl 2 in
                   exact_no_check (mkApp(mkVar idna,[|mkVar ida|])) gl)));
            tclIDTAC]));
       tclIDTAC])) { gls with Evd.sigma; }
let absurd c = Proofview.V82.tactic (absurd c)

(* Contradiction *)

let filter_hyp f tac =
  let rec seek = function
    | [] -> Proofview.tclZERO Not_found
    | (id,_,t)::rest when f t -> tac id
    | _::rest -> seek rest in
  Proofview.Goal.hyps >>= fun hyps ->
  seek (Environ.named_context_of_val hyps)

let contradiction_context =
  Proofview.tclEVARMAP >= fun sigma ->
  Proofview.Goal.env >>= fun env ->
  let rec seek_neg l = match l with
    | [] ->  Proofview.tclZERO (UserError ("" , Pp.str"No such contradiction"))
    | (id,_,typ)::rest ->
	let typ = whd_betadeltaiota env sigma typ in
	if is_empty_type typ then
	  simplest_elim (mkVar id)
	else match kind_of_term typ with
	  | Prod (na,t,u) when is_empty_type u ->
	      (Proofview.tclORELSE
                 begin
                   Tacmach.New.pf_apply is_conv_leq >>= fun is_conv_leq ->
	           filter_hyp (fun typ -> is_conv_leq typ t)
		     (fun id' -> simplest_elim (mkApp (mkVar id,[|mkVar id'|])))
                 end
                 begin function
	           | Not_found -> seek_neg rest
                   | e -> Proofview.tclZERO e
                 end)
	  | _ -> seek_neg rest
  in
  Proofview.Goal.hyps >>= fun hyps ->
  let hyps = Environ.named_context_of_val hyps in
  seek_neg hyps

let is_negation_of env sigma typ t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (na,t,u) -> is_empty_type u && is_conv_leq env sigma typ t
    | _ -> false

let contradiction_term (c,lbind as cl) =
  Proofview.tclEVARMAP >= fun sigma ->
  Proofview.Goal.env >>= fun env ->
  Tacmach.New.pf_apply Typing.type_of >>= fun type_of ->
  try (* type_of can raise exceptions. *)
  let typ = type_of c in
  let _, ccl = splay_prod env sigma typ in
  if is_empty_type ccl then
    Tacticals.New.tclTHEN (elim false cl None) (Proofview.V82.tactic (tclTRY assumption))
  else
    Proofview.tclORELSE
      begin
        if lbind = NoBindings then
	  filter_hyp (is_negation_of env sigma typ)
	    (fun id -> simplest_elim (mkApp (mkVar id,[|c|])))
        else
	  Proofview.tclZERO Not_found
      end
      begin function
        | Not_found -> Proofview.tclZERO (Errors.UserError ("",Pp.str"Not a contradiction."))
        | e -> Proofview.tclZERO e
      end
  with e when Proofview.V82.catchable_exception e -> Proofview.tclZERO e

let contradiction = function
  | None -> Tacticals.New.tclTHEN intros contradiction_context
  | Some c -> contradiction_term c
