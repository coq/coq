(* Checks syntax of Hints commands *)
(* Checks that qualified names are accepted *)

(* New-style syntax *)
Hint Resolve eq_refl: core arith.
Hint Immediate eq_trans.
Hint Unfold eq_sym: core.
Hint Constructors eq: foo bar.
Hint Extern 3 (_ = _) => apply eq_refl: foo bar.

(* Old-style syntax *)
Hint Resolve eq_refl eq_sym.
Hint Resolve eq_refl eq_sym: foo.
Hint Immediate eq_refl eq_sym.
Hint Immediate eq_refl eq_sym: foo.
Hint Unfold fst eq_sym.
Hint Unfold fst eq_sym: foo.

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
  Fail Timeout 2 apply _. (* 3.7s *)
  
Hint Cut [!*; (a_is_b | b_is_c | c_is_d | d_is_e) ;
  (a_compose | b_compose | c_compose | d_compose | e_compose)] : typeclass_instances.

  Timeout 2 Fail apply _. (* 0.06s *)
Abort.
End HintCut.
