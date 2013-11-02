(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*                              EqDecide                               *)
(*   A tactic for deciding propositional equality on inductive types   *)
(*                           by Eduardo Gimenez                        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Errors
open Util
open Names
open Namegen
open Term
open Declarations
open Tactics
open Tacticals
open Hiddentac
open Auto
open Matching
open Hipattern
open Tacmach
open Coqlib

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

let clear_last = (onLastHyp (fun c -> (clear [destVar c])))

let choose_eq eqonleft =
  if eqonleft then h_simplest_left else h_simplest_right
let choose_noteq eqonleft =
  if eqonleft then h_simplest_right else h_simplest_left

let mkBranches c1 c2 =
  Tacticals.New.tclTHENLIST
    [Proofview.V82.tactic (generalize [c2]);
     h_simplest_elim c1;
     intros;
     Tacticals.New.onLastHyp h_simplest_case;
     Proofview.V82.tactic clear_last;
     intros]

let solveNoteqBranch side =
  Tacticals.New.tclTHEN (choose_noteq side)
    (Tacticals.New.tclTHEN introf
      (Tacticals.New.onLastHypId (fun id -> Extratactics.discrHyp id)))

(* Constructs the type {c1=c2}+{~c1=c2} *)

let mkDecideEqGoal eqonleft op rectype c1 c2 g =
  let equality    = mkApp(build_coq_eq(), [|rectype; c1; c2|]) in
  let disequality = mkApp(build_coq_not (), [|equality|]) in
  if eqonleft then mkApp(op, [|equality; disequality |])
  else mkApp(op, [|disequality; equality |])


(* Constructs the type (x1,x2:R){x1=x2}+{~x1=x2} *)

let mkGenDecideEqGoal rectype g =
  let hypnames = pf_ids_of_hyps g in
  let xname    = next_ident_away (Id.of_string "x") hypnames
  and yname    = next_ident_away (Id.of_string "y") hypnames in
  (mkNamedProd xname rectype
     (mkNamedProd yname rectype
        (mkDecideEqGoal true (build_coq_sumbool ())
          rectype (mkVar xname) (mkVar yname) g)))

let eqCase tac =
  (Tacticals.New.tclTHEN intro
  (Tacticals.New.tclTHEN (Tacticals.New.onLastHyp Equality.rewriteLR)
  (Tacticals.New.tclTHEN (Proofview.V82.tactic clear_last)
  tac)))

let diseqCase eqonleft =
  let diseq  = Id.of_string "diseq" in
  let absurd = Id.of_string "absurd" in
  (Tacticals.New.tclTHEN (intro_using diseq)
  (Tacticals.New.tclTHEN (choose_noteq eqonleft)
  (Tacticals.New.tclTHEN  (Proofview.V82.tactic red_in_concl)
  (Tacticals.New.tclTHEN  (intro_using absurd)
  (Tacticals.New.tclTHEN  (Proofview.V82.tactic (h_simplest_apply (mkVar diseq)))
  (Tacticals.New.tclTHEN  (Extratactics.injHyp absurd)
            (full_trivial [])))))))

open Proofview.Notations

(* spiwack: a small wrapper around [Hipattern]. *)

let match_eqdec c =
  try Proofview.tclUNIT (match_eqdec c)
  with PatternMatchingFailure -> Proofview.tclZERO PatternMatchingFailure

(* /spiwack *)

let solveArg eqonleft op a1 a2 tac =
  Tacmach.New.of_old (fun g -> pf_type_of g a1) >>- fun rectype ->
  Tacmach.New.of_old (fun g -> mkDecideEqGoal eqonleft op rectype a1 a2 g) >>- fun decide ->
  let subtacs =
    if eqonleft then [eqCase tac;diseqCase eqonleft;default_auto]
    else [diseqCase eqonleft;eqCase tac;default_auto] in
  (Tacticals.New.tclTHENS (Proofview.V82.tactic (h_elim_type decide)) subtacs)

let solveEqBranch rectype =
  Proofview.tclORELSE
    begin
      Proofview.Goal.concl >>- fun concl ->
      match_eqdec concl >= fun (eqonleft,op,lhs,rhs,_) ->
      let (mib,mip) = Global.lookup_inductive rectype in
      let nparams   = mib.mind_nparams in
      let getargs l = List.skipn nparams (snd (decompose_app l)) in
      let rargs   = getargs rhs
      and largs   = getargs lhs in
      List.fold_right2
        (solveArg eqonleft op) largs rargs
        (Tacticals.New.tclTHEN (choose_eq eqonleft) h_reflexivity)
    end
    begin function
      | PatternMatchingFailure -> Proofview.tclZERO (UserError ("",Pp.str"Unexpected conclusion!"))
      | e -> Proofview.tclZERO e
    end

(* The tactic Decide Equality *)

let hd_app c = match kind_of_term c with
  | App (h,_) -> h
  | _ -> c

let decideGralEquality =
  Proofview.tclORELSE
    begin
      Proofview.Goal.concl >>- fun concl ->
      match_eqdec concl >= fun eqonleft,_,c1,c2,typ ->
      Tacmach.New.of_old (fun g -> hd_app (pf_compute g typ)) >>- fun headtyp ->
      begin match kind_of_term headtyp with
      | Ind mi -> Proofview.tclUNIT mi
      | _ -> Proofview.tclZERO (UserError ("",Pp.str"This decision procedure only works for inductive objects."))
      end >= fun rectype ->
      (Tacticals.New.tclTHEN
         (mkBranches c1 c2)
         (Tacticals.New.tclORELSE (solveNoteqBranch eqonleft) (solveEqBranch rectype)))
    end
    begin function
      | PatternMatchingFailure ->
          Proofview.tclZERO (UserError ("", Pp.str"The goal must be of the form {x<>y}+{x=y} or {x=y}+{x<>y}."))
      | e -> Proofview.tclZERO e
    end

let decideEqualityGoal = Tacticals.New.tclTHEN intros decideGralEquality

let decideEquality rectype =
  Tacmach.New.of_old (mkGenDecideEqGoal rectype) >>- fun decide ->
  (Tacticals.New.tclTHENS (Proofview.V82.tactic (cut decide)) [default_auto;decideEqualityGoal])


(* The tactic Compare *)

let compare c1 c2 =
  Tacmach.New.of_old (fun g -> pf_type_of g c1) >>- fun rectype ->
  Tacmach.New.of_old (fun g -> mkDecideEqGoal true (build_coq_sumbool ()) rectype c1 c2 g) >>- fun decide ->
  (Tacticals.New.tclTHENS (Proofview.V82.tactic (cut decide))
            [(Tacticals.New.tclTHEN  intro
             (Tacticals.New.tclTHEN (Tacticals.New.onLastHyp simplest_case)
                       (Proofview.V82.tactic clear_last)));
             decideEquality rectype])


(* User syntax *)

TACTIC EXTEND decide_equality
| [ "decide" "equality" ] -> [ decideEqualityGoal ]
END

TACTIC EXTEND compare
| [ "compare" constr(c1) constr(c2) ] -> [ compare c1 c2 ]
END
