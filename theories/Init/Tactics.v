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

(* A shorter name for generalize + clear, can be seen as an anti-intro *)

Tactic Notation "revert" ne_hyp_list(l) := generalize l; clear l.

(* to contradict an hypothesis without copying its type. *)

Ltac absurd_hyp h := 
  let T := type of h in 
  absurd T.

(* Transforming a negative goal [ H:~A |- ~B ] into a positive one [ B |- A ]*)

Ltac swap H := intro; apply H; clear H.

(* A case with no loss of information. *)

Ltac case_eq x := generalize (refl_equal x); pattern x at -1; case x.

(* A tactic for easing the use of lemmas f_equal, f_equal2, ... *)

Ltac f_equal := 
  let cg := try congruence in
  let r := try reflexivity in 
  match goal with 
   | |- ?f ?a = ?f' ?a' => cut (a=a'); [cg|r]
   | |- ?f ?a ?b = ?f' ?a' ?b' => 
      cut (b=b');[cut (a=a');[cg|r]|r]
   | |- ?f ?a ?b ?c = ?f' ?a' ?b' ?c'=> 
      cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]
   | |- ?f ?a ?b ?c ?d= ?f' ?a' ?b' ?c' ?d'=> 
      cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]|r]
  | |- ?f ?a ?b ?c ?d ?e= ?f' ?a' ?b' ?c' ?d' ?e'=> 
      cut (e=e');[cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]|r]|r]
   | _ => idtac
  end.

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
