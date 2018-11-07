(* Checks syntax of Hints commands *)
(* Old-style syntax *)
Hint Resolve eq_refl eq_sym.
Hint Resolve eq_refl eq_sym: foo.
Hint Immediate eq_refl eq_sym.
Hint Immediate eq_refl eq_sym: foo.
Hint Unfold fst eq_sym.
Hint Unfold fst eq_sym: foo.

(* Checks that qualified names are accepted *)

(* New-style syntax *)
Hint Resolve eq_refl: core arith.
Hint Immediate eq_trans.
Hint Unfold eq_sym: core.
Hint Constructors eq: foo bar.
Hint Extern 3 (_ = _) => apply eq_refl: foo bar.

(* Extended new syntax with patterns *)
Hint Resolve eq_refl | 4 (_ = _) : baz.
Hint Resolve eq_sym eq_trans : baz.
Hint Extern 3 (_ = _) => apply eq_sym : baz.

Parameter pred : nat -> Prop.
Parameter pred0 : pred 0.
Parameter f : nat -> nat.
Parameter predf : forall n, pred n -> pred (f n).

(* No conversion on let-bound variables and constants in pred (the default) *)
Hint Resolve pred0 | 1 (pred _) : pred.
Hint Resolve predf | 0 : pred.

(* Allow full conversion on let-bound variables and constants *)
Create HintDb predconv discriminated.
Hint Resolve pred0 | 1 (pred _) : predconv.
Hint Resolve predf | 0 : predconv.

Goal exists n, pred n.
  eexists.
  Set Typeclasses Filtered Unification.
  Set Typeclasses Debug Verbosity 2.
  (* predf is not tried as it doesn't match the goal *)
  typeclasses eauto with pred.
Qed.

Parameter predconv : forall n, pred n -> pred (0 + S n).

(* The inferred pattern contains 0 + ?n, syntactic match will fail to see convertible
 terms *)
Hint Resolve pred0 : pred2.
Hint Resolve predconv : pred2.

(** In this database we allow predconv to apply to pred (S _) goals, more generally
  than the inferred pattern (pred (0 + S _)). *)
Create HintDb pred2conv discriminated.
Hint Resolve pred0 : pred2conv.
Hint Resolve predconv | 1 (pred (S _)) : pred2conv.

Goal pred 3.
  Fail typeclasses eauto with pred2.
  typeclasses eauto with pred2conv.
Abort.

Set Typeclasses Filtered Unification.
Set Typeclasses Debug Verbosity 2.
Hint Resolve predconv | 1 (pred _) : pred.
Hint Resolve predconv | 1 (pred (S _)) : predconv.
Test Typeclasses Limit Intros.
Goal pred 3.
  (* predf is not tried as it doesn't match the goal *)
  (* predconv is tried but fails as the transparent state doesn't allow
     unfolding + *)
  Fail typeclasses eauto with pred.
  (* Here predconv succeeds as it matches (pred (S _)) and then
     full unification is allowed *)
  typeclasses eauto with predconv.
Qed.

(** The other way around: goal contains redexes instead of instances *)
Goal exists n, pred (0 + n).
  eexists.
  (* pred0 (pred _) matches the goal *)
  typeclasses eauto with predconv.
Qed.


(* Checks that local names are accepted *)
Section A.
  Remark Refl : forall (A : Set) (x : A), x = x.
  Proof. exact @eq_refl. Defined.
  Definition Sym := eq_sym.
  Let Trans := eq_trans.

  Hint Resolve Refl: foo.
  Hint Resolve Sym: bar.
  Hint Resolve Trans: foo2.

  Hint Immediate Refl.
  Hint Immediate Sym.
  Hint Immediate Trans.

  Hint Unfold Refl.
  Hint Unfold Sym.
  Hint Unfold Trans.

  Hint Resolve Sym Trans Refl.
  Hint Immediate Sym Trans Refl.
  Hint Unfold Sym Trans Refl.

End A.

Axiom a : forall n, n=0 <-> n<=0.

Hint Resolve -> a.
Goal forall n, n=0 -> n<=0.
auto.
Qed.


(* This example comes from Chlipala's ltamer *)
(* It used to fail from r12902 to r13112 since type_of started to call *)
(* e_cumul (instead of conv_leq) which was not able to unify "?id" and *)
(* "(fun x => x) ?id" *)

Notation "e :? pf" := (eq_rect _ (fun X : Set => X) e _ pf)
  (no associativity, at level 90).

Axiom cast_coalesce :
  forall (T1 T2 T3 : Set) (e : T1) (pf1 : T1 = T2) (pf2 : T2 = T3),
  ((e :? pf1) :? pf2) = (e :? trans_eq pf1 pf2).

Hint Rewrite cast_coalesce : ltamer.

Require Import Program.
Module HintCut.
Class A (f : nat -> nat) := a : True.
Class B (f : nat -> nat) := b : True.
Class C (f : nat -> nat) := c : True.
Class D (f : nat -> nat) := d : True.
Class E (f : nat -> nat) := e : True.

Instance a_is_b f : A f -> B f.
Proof. easy. Qed.
Instance b_is_c f : B f -> C f.
Proof. easy. Qed.
Instance c_is_d f : C f -> D f.
Proof. easy. Qed.
Instance d_is_e f : D f -> E f.
Proof. easy. Qed.

Instance a_compose f g : A f -> A g -> A (compose f g).
Proof. easy. Qed.
Instance b_compose f g : B f -> B g -> B (compose f g).
Proof. easy. Qed.
Instance c_compose f g : C f -> C g -> C (compose f g).
Proof. easy. Qed.
Instance d_compose f g : D f -> D g -> D (compose f g).
Proof. easy. Qed.
Instance e_compose f g : E f -> E g -> E (compose f g).
Proof. easy. Qed.

Instance a_id : A id.
Proof. easy. Qed.

Instance foo f :
  E (id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘
     id ∘ id ∘ id ∘ id ∘ id ∘ f ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id ∘ id).
Proof.
Hint Cut [_* (a_is_b | b_is_c | c_is_d | d_is_e)
                 (a_compose | b_compose | c_compose | d_compose | e_compose)] : typeclass_instances.

  Timeout 1 Fail apply _. (* 0.06s *)
Abort.
End HintCut.


(* Check that auto-like tactics do not prefer "eq_refl" over more complex solutions, *)
(* e.g. those tactics when considering a goal with existential varibles *)
(* like "m = ?n" won't pick "plus_n_O" hint over "eq_refl" hint. *)
(* See this Coq club post for more detail: *)
(* https://sympa.inria.fr/sympa/arc/coq-club/2017-12/msg00103.html *)

Goal forall (m : nat), exists n, m = n /\ m = n.
  intros m; eexists; split; [trivial | reflexivity].
Qed.

Section HintTransparent.

  Definition fn (x : nat) := S x.

  Create HintDb trans.

  Hint Resolve eq_refl | (_ = _) : trans.

  (* No reduction *)
  Hint Variables Opaque : trans.  Hint Constants Opaque : trans.

  Goal forall x : nat, fn x = S x.
  Proof.
    intros.
    Fail typeclasses eauto with trans.
    unfold fn.
    typeclasses eauto with trans.
  Qed.

  (** Now allow unfolding fn *)
  Hint Constants Transparent : trans.

  Goal forall x : nat, fn x = S x.
  Proof.
    intros.
    typeclasses eauto with trans.
  Qed.

End HintTransparent.
