open Util
open Term
open Proof_type
open Hipattern
open Tacmach
open Tacticals
open Tactics
open Coqlib

(* Contradiction *)

let contradiction_on_hyp id gl =
  let hyp = pf_get_hyp_typ gl id in
  if is_empty_type hyp then
    simplest_elim (mkVar id) gl
  else 
    error "Not a contradiction"

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

let contradiction gls = 
  tclTHENLIST [ intros; elim_type (build_coq_False ()); assumption ] gls
