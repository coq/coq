(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Pp
open Util

open Proof_trees
open Tacmach
open Tactics
open Tacinterp
open Tacticals
open Prove
open Ccidpc

let rec intros_forall gls = 
  let t = pf_concl gls
  in if is_forall_term t
     then ((tclTHEN intro (intros_forall))) gls
     else tclIDTAC gls

let dPC_nq gls =
    let f = dpc_of_cci_fmla gls (pf_concl gls) in
    try let pf = prove_f f in 
      	tradpf [] [] pf gls
    with Not_provable_in_DPC s -> errorlabstrm "dpc__DPC_nq"
            (str "Not provable in Direct Predicate Calculus")
 
       | No_intuitionnistic_proof n  -> errorlabstrm "dpc__DPC_nq"
            ((str "Found ") ++
	     (str (string_of_int n)) ++
	     (str " classical proof(s) but no intuitionnistic one !"))


let dPC =
  ((tclTHEN (intros_forall) (dPC_nq))) 


let dPC_l lcom =
  (tclTHEN (intros_forall) 
      (tclTHEN (generalize lcom) (dPC))) 

(*
let dPC_tac = hide_atomic_tactic "DPC" dPC

let dPC_l_tac = hide_tactic "DPC_l" 
    (fun lcom -> dPC_l lcom)
*)

TACTIC EXTEND Linear 
[ "Linear" ]->[(dPC)]
|[ "Linear" "with" ne_constr_list(l) ] -> [(dPC_l l)]
END



