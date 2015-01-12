(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

(* Absurd *)

let mk_absurd_proof t =
  let id = Namegen.default_dependent_ident in
  mkLambda (Names.Name id,mkApp(build_coq_not (),[|t|]),
    mkLambda (Names.Name id,t,mkApp (mkRel 2,[|mkRel 1|])))

let absurd c =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let j = Retyping.get_judgment_of env sigma c in
    let sigma, j = Coercion.inh_coerce_to_sort Loc.ghost env sigma j in
    let t = j.Environ.utj_val in
    Tacticals.New.tclTHENLIST [
      Proofview.Unsafe.tclEVARS sigma;
      elim_type (build_coq_False ());
      Simple.apply (mk_absurd_proof t)
    ]
  end

let absurd c = absurd c

(* Contradiction *)

(** [f] does not assume its argument to be [nf_evar]-ed. *)
let filter_hyp f tac =
  let rec seek = function
    | [] -> Proofview.tclZERO Not_found
    | (id,_,t)::rest when f t -> tac id
    | _::rest -> seek rest in
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps (Proofview.Goal.assume gl) in
    seek hyps
  end

let contradiction_context =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let rec seek_neg l = match l with
      | [] ->  Proofview.tclZERO (UserError ("" , Pp.str"No such contradiction"))
      | (id,_,typ)::rest ->
          let typ = nf_evar sigma typ in
	  let typ = whd_betadeltaiota env sigma typ in
	  if is_empty_type typ then
	    simplest_elim (mkVar id)
	  else match kind_of_term typ with
	  | Prod (na,t,u) when is_empty_type u ->
	      (Proofview.tclORELSE
                 (Proofview.Goal.enter begin fun gl ->
                   let is_conv_leq = Tacmach.New.pf_apply is_conv_leq gl in
	           filter_hyp (fun typ -> is_conv_leq typ t)
		     (fun id' -> simplest_elim (mkApp (mkVar id,[|mkVar id'|])))
                 end)
                 begin function (e, info) -> match e with
	           | Not_found -> seek_neg rest
                   | e -> Proofview.tclZERO ~info e
                 end)
	  | _ -> seek_neg rest
    in
    let hyps = Proofview.Goal.hyps (Proofview.Goal.assume gl) in
    seek_neg hyps
  end

let is_negation_of env sigma typ t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (na,t,u) ->
      let u = nf_evar sigma u in
      is_empty_type u && is_conv_leq env sigma typ t
    | _ -> false

let contradiction_term (c,lbind as cl) =
  Proofview.Goal.nf_enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let type_of = Tacmach.New.pf_type_of gl in
    let typ = type_of c in
    let _, ccl = splay_prod env sigma typ in
    if is_empty_type ccl then
      Tacticals.New.tclTHEN
        (elim false None cl None)
        (Tacticals.New.tclTRY assumption)
    else
      Proofview.tclORELSE
        begin
          if lbind = NoBindings then
            filter_hyp (is_negation_of env sigma typ)
              (fun id -> simplest_elim (mkApp (mkVar id,[|c|])))
          else
            Proofview.tclZERO Not_found
        end
        begin function (e, info) -> match e with
          | Not_found -> Proofview.tclZERO (Errors.UserError ("",Pp.str"Not a contradiction."))
          | e -> Proofview.tclZERO ~info e
        end
  end

let contradiction = function
  | None -> Tacticals.New.tclTHEN intros contradiction_context
  | Some c -> contradiction_term c
