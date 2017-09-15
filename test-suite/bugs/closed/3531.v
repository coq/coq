Require Import TestSuite.admit.
(* File reduced by coq-bug-finder from original input, then from 270 lines to
198 lines, then from 178 lines to 82 lines, then from 88 lines to 59 lines *)
(* coqc version trunk (August 2014) compiled on Aug 19 2014 14:40:15 with OCaml
4.01.0
  coqtop version cagnode17:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk
(56ece74efc25af1b0e09265f3c7fcf74323abcaf) *)
Require Import Coq.Lists.List.
Set Implicit Arguments.
Definition mem := nat -> option nat.
Definition pred := mem -> Prop.
Delimit Scope pred_scope with pred.
Definition exis A (p : A -> pred) : pred := fun m => exists x, p x m.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) :
pred_scope.
Definition emp : pred := fun m => forall a, m a = None.
Definition lift_empty (P : Prop) : pred := fun m => P /\ forall a, m a = None.
Notation "[[ P ]]" := (lift_empty P) : pred_scope.
Definition pimpl (p q : pred) := forall m, p m -> q m.
Notation "p ==> q" := (pimpl p%pred q%pred) (right associativity, at level 90).
Definition piff (p q : pred) : Prop := (p ==> q) /\ (q ==> p).
Notation "p <==> q" := (piff p%pred q%pred) (at level 90).
Parameter sep_star : pred -> pred -> pred.
Infix "*" := sep_star : pred_scope.
Definition memis (m : mem) : pred := eq m.
Definition mptsto (m : mem) (a : nat) (v : nat) := m a = Some v.
Notation "m @ a |-> v" := (mptsto m a v) (a at level 34, at level 35).
Lemma piff_trans: forall a b c, (a <==> b) -> (b <==> c) -> (a <==> c).
Admitted.
Lemma piff_refl: forall a, (a <==> a).
Admitted.
Definition stars (ps : list pred) := fold_left sep_star ps emp.
Lemma flatten_exists: forall T PT p ps P,
 (forall (a:T), (p a <==> exists (x:PT), stars (ps a x) * [[P a x]]))
 -> (exists (a:T), p a) <==>
     (exists (x:(T*PT)), stars (ps (fst x) (snd x)) * [[P (fst x) (snd x)]]).
Admitted.
Goal forall b, (exists e1 e2 e3,
      (exists (m : mem) (v : nat) (F : pred), b)
        <==> (exists x : e1, stars (e2 x) * [[e3 x]])).
 intros. 
 Set Printing Universes.
 Show Universes.
 do 3 eapply ex_intro.  
 eapply piff_trans; [ apply flatten_exists | apply piff_refl ]; intros.
 eapply piff_trans; [ apply flatten_exists | apply piff_refl ]; intros.
 eapply piff_trans; [ apply flatten_exists | apply piff_refl ]; intros.
 assert (H : False) by (clear; admit); destruct H.
 Grab Existential Variables.
 admit.
 admit.
 admit.
 Show Universes.
Time Qed.
