(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Notations.
Require Import Logic.

(** Useful tactics *)

(* Rewriting in all hypothesis. *)

Ltac rewrite_all Eq := match type of Eq with
  ?a = ?b =>
     generalize Eq; clear Eq;
     match goal with
    | H : context [a] |- _ => intro Eq; rewrite Eq in H; rewrite_all Eq
    | _ => intro Eq; try rewrite Eq
    end
 end.

Ltac rewrite_all_rev Eq := match type of Eq with
  ?a = ?b =>
     generalize Eq; clear Eq;
     match goal with
    | H : context [b] |- _ => intro Eq; rewrite <- Eq in H; rewrite_all_rev Eq
    | _ => intro Eq; try rewrite <- Eq
    end
 end.

Tactic Notation "rewrite_all" "<-" constr(H) := rewrite_all_rev H.

(* A case with no loss of information. *)

Ltac case_eq x := generalize (refl_equal x); pattern x at -1; case x.

(* A tactic for easing the use of lemmas f_equal, f_equal2, ... *)

Ltac f_equal := 
  let des := destruct 1 || intro in
  let r := try reflexivity in 
  match goal with 
   | |- ?f ?a = ?f' ?a' => cut (a=a'); des; r
   | |- ?f ?a ?b = ?f' ?a' ?b' => 
      cut (b=b');[cut (a=a');[do 2 des; r|r]|r]
   | |- ?f ?a ?b ?c = ?f' ?a' ?b' ?c'=> 
      cut (c=c');[cut (b=b');[cut (a=a');[do 3 des; r|r]|r]|r]
   | |- ?f ?a ?b ?c ?d= ?f' ?a' ?b' ?c' ?d'=> 
      cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[do 4 des; r|r]|r]|r]|r]
  | |- ?f ?a ?b ?c ?d ?e= ?f' ?a' ?b' ?c' ?d' ?e'=> 
      cut (e=e');[cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[do 5 des; r|r]|r]|r]|r]|r]
   | _ => idtac
  end.

