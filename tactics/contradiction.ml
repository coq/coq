(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open EConstr
open Hipattern
open Tactics
open Coqlib
open Reductionops
open Proofview.Notations

module NamedDecl = Context.Named.Declaration

(* Absurd *)

let mk_absurd_proof coq_not t =
  let id = Namegen.default_dependent_ident in
  mkLambda (Names.Name id,mkApp(coq_not,[|t|]),
    mkLambda (Names.Name id,t,mkApp (mkRel 2,[|mkRel 1|])))

let absurd c =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let j = Retyping.get_judgment_of env sigma c in
    let sigma, j = Coercion.inh_coerce_to_sort env sigma j in
    let t = j.Environ.utj_val in
    Proofview.Unsafe.tclEVARS sigma <*>
    Tacticals.New.pf_constr_of_global (build_coq_not ()) >>= fun coqnot ->
    Tacticals.New.pf_constr_of_global (build_coq_False ()) >>= fun coqfalse ->
    Tacticals.New.tclTHENLIST [
      elim_type coqfalse;
      Simple.apply (mk_absurd_proof coqnot t)
    ]
  end

let absurd c = absurd c

(* Contradiction *)

(** [f] does not assume its argument to be [nf_evar]-ed. *)
let filter_hyp f tac =
  let rec seek = function
    | [] -> Proofview.tclZERO Not_found
    | d::rest when f (NamedDecl.get_type d) -> tac (NamedDecl.get_id d)
    | _::rest -> seek rest in
  Proofview.Goal.enter begin fun gl ->
    let hyps = Proofview.Goal.hyps gl in
    seek hyps
  end

let contradiction_context =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    let rec seek_neg l = match l with
      | [] ->  Tacticals.New.tclZEROMSG (Pp.str"No such contradiction")
      | d :: rest ->
          let id = NamedDecl.get_id d in
          let typ = nf_evar sigma (NamedDecl.get_type d) in
	  let typ = whd_all env sigma typ in
	  if is_empty_type sigma typ then
	    simplest_elim (mkVar id)
	  else match EConstr.kind sigma typ with
	  | Prod (na,t,u) when is_empty_type sigma u ->
             let is_unit_or_eq = match_with_unit_or_eq_type sigma t in
	     Tacticals.New.tclORELSE
               (match is_unit_or_eq with
               | Some _ ->
                   let hd,args = decompose_app sigma t in
                   let (ind,_ as indu) = destInd sigma hd in
                   let nparams = Inductiveops.inductive_nparams_env env ind in
                   let params = Util.List.firstn nparams args in
                   let p = applist ((mkConstructUi (indu,1)), params) in
                   (* Checking on the fly that it type-checks *)
                   simplest_elim (mkApp (mkVar id,[|p|]))
               | None ->
                 Tacticals.New.tclZEROMSG (Pp.str"Not a negated unit type."))
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
    let hyps = Proofview.Goal.hyps gl in
    seek_neg hyps
  end

let is_negation_of env sigma typ t =
  match EConstr.kind sigma (whd_all env sigma t) with
    | Prod (na,t,u) ->
      is_empty_type sigma u && is_conv_leq env sigma typ t
    | _ -> false

let contradiction_term (c,lbind as cl) =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.New.project gl in
    let env = Proofview.Goal.env gl in
    let type_of = Tacmach.New.pf_unsafe_type_of gl in
    let typ = type_of c in
    let _, ccl = splay_prod env sigma typ in
    if is_empty_type sigma ccl then
      Tacticals.New.tclTHEN
        (elim false None cl None)
        (Tacticals.New.tclTRY assumption)
    else
      Proofview.tclORELSE
        begin
          if lbind = Tactypes.NoBindings then
            filter_hyp (fun c -> is_negation_of env sigma typ c)
              (fun id -> simplest_elim (mkApp (mkVar id,[|c|])))
          else
            Proofview.tclZERO Not_found
        end
        begin function (e, info) -> match e with
          | Not_found -> Tacticals.New.tclZEROMSG (Pp.str"Not a contradiction.")
          | e -> Proofview.tclZERO ~info e
        end
  end

let contradiction = function
  | None -> Tacticals.New.tclTHEN intros contradiction_context
  | Some c -> contradiction_term c
