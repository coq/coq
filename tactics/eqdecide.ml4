(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Util
open Names
open Nameops
open Term
open Declarations
open Tactics
open Tacticals
open Hiddentac
open Equality
open Auto
open Pattern
open Matching
open Hipattern
open Coqlib

(* arnaud: trucs factices *)
module Refiner =
  struct
    let abstract_extended_tactic _ = Util.anomaly "Eqdecide.abstract_extended_tactic: fantome"
  end
let pf_ids_of_hyps _ = Util.anomaly "Eqdecide.pf_ids_of_hyps: fantome"
let pf_type_of _ = Util.anomaly "Eqdecide.pf_type_of: fantome"
let pf_concl _ = Util.anomaly "Eqdecide.pf_concl: fantome"
let pf_compute _ = Util.anomaly "Eqdecide.pf_compute: fantome"
(* arnaud: /trucs factices *)

(* This file containts the implementation of the tactics ``Decide
   Equality'' and ``Compare''. They can be used to decide the
   propositional equality of two objects that belongs to a small
   inductive datatype --i.e., an inductive set such that all the
   arguments of its constructors are non-functional sets.

   The procedure for proving (x,y:R){x=y}+{~x=y} can be scketched as
   follows:
   1. Eliminate x and then y.
   2. Try discrimination to solve those goals where x and y has
      been introduced by different constructors.
   3. If x and y have been introduced by the same constructor,
      then analyse one by one the corresponding pairs of arguments.
      If they are equal, rewrite one into the other. If they are
      not, derive a contradiction from the injectiveness of the
      constructor. 
   4. Once all the arguments have been rewritten, solve the remaining half 
      of the disjunction by reflexivity.

   Eduardo Gimenez (30/3/98).
*)

let clear_last = (tclLAST_HYP (fun c -> (clear [destVar c])))

let choose_eq eqonleft = 
  if eqonleft then h_simplest_left else h_simplest_right
let choose_noteq eqonleft =
  if eqonleft then h_simplest_right else h_simplest_left

let mkBranches c1 c2 = 
  tclTHENSEQ
    [generalize [c2];
     h_simplest_elim c1;
     intros;
     tclLAST_HYP h_simplest_case;
     clear_last;
     intros]

let solveNoteqBranch side = 
  tclTHEN (choose_noteq side)
    (tclTHEN (intro_force true)
      (onLastHyp (fun id -> Extratactics.h_discrHyp (Rawterm.NamedHyp id))))

let h_solveNoteqBranch side =
  Refiner.abstract_extended_tactic "solveNoteqBranch" [] 
    (solveNoteqBranch side)

(* Constructs the type {c1=c2}+{~c1=c2} *)

let mkDecideEqGoal eqonleft op rectype c1 c2 g = 
  let equality    = mkApp(build_coq_eq(), [|rectype; c1; c2|]) in
  let disequality = mkApp(build_coq_not (), [|equality|]) in
  if eqonleft then mkApp(op, [|equality; disequality |])
  else mkApp(op, [|disequality; equality |])


(* Constructs the type (x1,x2:R){x1=x2}+{~x1=x2} *)

let mkGenDecideEqGoal rectype g = 
  let hypnames = pf_ids_of_hyps g in 
  let xname    = next_ident_away (id_of_string "x") hypnames
  and yname    = next_ident_away (id_of_string "y") hypnames in
  (mkNamedProd xname rectype 
     (mkNamedProd yname rectype 
        (mkDecideEqGoal true (build_coq_sumbool ())
          rectype (mkVar xname) (mkVar yname) g)))

let eqCase tac = 
  (tclTHEN intro  
  (tclTHEN (tclLAST_HYP Equality.rewriteLR)
  (tclTHEN clear_last 
  tac)))

let diseqCase eqonleft =
  Util.anomaly "Eqdecide.diseqCase: à restaurer"
  (* arnaud : à restaurer: 
  let diseq  = id_of_string "diseq" in
  let absurd = id_of_string "absurd" in 
  (tclTHEN (intro_using diseq)
  (tclTHEN (choose_noteq eqonleft)
  (tclTHEN  red_in_concl
  (tclTHEN  (intro_using absurd)
  (tclTHEN  (h_simplest_apply (mkVar diseq))
  (tclTHEN  (Extratactics.h_injHyp (Rawterm.NamedHyp absurd))
            (full_trivial [])))))))
  *)

let solveArg eqonleft op a1 a2 tac = 
  Util.anomaly "Eqdecide.solveArg: à restaurer"
  (* arnaud: à restaurer:
  let rectype = pf_type_of g a1 in
  let decide  = mkDecideEqGoal eqonleft op rectype a1 a2 g in
  let subtacs = 
    if eqonleft then [eqCase tac;diseqCase eqonleft;default_auto] 
    else [diseqCase eqonleft;eqCase tac;default_auto] in
  (tclTHENS (h_elim_type decide) subtacs) g
  *)

let solveEqBranch rectype g =
  try
    let (eqonleft,op,lhs,rhs,_) = match_eqdec (pf_concl g) in
    let (mib,mip) = Global.lookup_inductive rectype in
    let nparams   = mib.mind_nparams in
    let getargs l = list_skipn nparams (snd (decompose_app l)) in
    let rargs   = getargs rhs
    and largs   = getargs lhs in 
    List.fold_right2 
      (solveArg eqonleft op) largs rargs
      (tclTHEN (choose_eq eqonleft) h_reflexivity) g
  with PatternMatchingFailure -> error "Unexpected conclusion!"

(* The tactic Decide Equality *)

let hd_app c = match kind_of_term c with
  | App (h,_) -> h
  | _ -> c

let decideGralEquality g =
  try
    let eqonleft,_,c1,c2,typ = match_eqdec (pf_concl g) in
    let headtyp = hd_app (pf_compute g typ) in
    let rectype =
      match kind_of_term headtyp with
        | Ind mi -> mi
	| _ -> error "This decision procedure only works for inductive objects"
    in
    (tclTHEN
      (mkBranches c1 c2)
      (tclORELSE (h_solveNoteqBranch eqonleft) (solveEqBranch rectype)))
    g
  with PatternMatchingFailure ->
    error "The goal must be of the form {x<>y}+{x=y} or {x=y}+{x<>y}"

let decideEqualityGoal = tclTHEN intros decideGralEquality

let decideEquality c1 c2 =
  Util.anomaly "Eqdecide.decideEquality: à restaurer" 
  (* arnaud: à restaurer:
  let rectype = (pf_type_of g c1) in     
  let decide  = mkGenDecideEqGoal rectype g in  
  (tclTHENS (cut decide) [default_auto;decideEqualityGoal]) g
  *)


(* The tactic Compare *)

let compare c1 c2 g = 
  let rectype = pf_type_of g c1 in
  let decide  = mkDecideEqGoal true (build_coq_sumbool ()) rectype c1 c2 g in  
  (tclTHENS (cut decide) 
            [(tclTHEN  intro 
             (tclTHEN (tclLAST_HYP simplest_case)
                       clear_last));
             decideEquality c1 c2]) g


(* User syntax *)

TACTIC EXTEND decide_equality
  [ "decide" "equality" constr(c1) constr(c2) ] -> [ Util.anomaly "Eqdecide.decide_equality: à restaurer" (* arnaud: decideEquality c1 c2 *) ]
| [ "decide" "equality" ] -> [ Util.anomaly "Eqdecide.decide_equality: à restaurer" (* arnaud: decideEqualityGoal *) ]
END

TACTIC EXTEND compare
| [ "compare" constr(c1) constr(c2) ] -> [ Util.anomaly "Eqdecide.compare: à restaurer" (* arnaud: compare c1 c2 *) ]
END
