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
   | |- ?f ?a ?b ?c ?d ?e ?f= ?f' ?a' ?b' ?c' ?d' ?e' ?f' => 
      cut (f=f');[cut (e=e');[cut (d=d');[cut (c=c');[cut (b=b');[cut (a=a');[cg|r]|r]|r]|r]|r]|r]
   | _ => idtac
  end.

(* Specializing universal hypothesis. 
   The word "specialize" is already used for a not-documented-anymore 
   tactic still used in some users contribs. Any idea for a better name?
*)

Tactic Notation "narrow" hyp(H) "with" constr(x) := 
 generalize (H x); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) := 
 generalize (H x y); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) constr(z):= 
 generalize (H x y z); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) constr(z) constr(t):= 
 generalize (H x y z t); clear H; intro H.
Tactic Notation "narrow" hyp(H) "with" constr(x) constr(y) constr(z) constr(t) constr(u):= 
 generalize (H x y z t u); clear H; intro H.

(* Rewriting in all hypothesis several times everywhere *)

Tactic Notation "rewrite_all" constr(eq) := repeat rewrite eq in *.
Tactic Notation "rewrite_all" "<-" constr(eq) := repeat rewrite <- eq in *.

(* Keeping a copy of an expression *)

Ltac remembertac x a :=
  let x := fresh x in
  let H := fresh "Heq" x in
  (set (x:=a) in *; assert (H: x=a) by reflexivity; clearbody x).

Tactic Notation "remember" constr(c) "as" ident(x) := remembertac x c.
