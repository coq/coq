Require Import ssreflect.

(* under <names>: {occs}[patt]<lemma>.
   under <names>: {occs}[patt]<lemma> by tac1.
   under <names>: {occs}[patt]<lemma> by [tac1 | ...].
 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom daemon : False. Ltac myadmit := case: daemon.

Module Mocks.

(* Mock bigop.v definitions to test the behavior of under with bigops
   without requiring mathcomp *)

Variant bigbody (R I : Type) : Type :=
  BigBody : forall (_ : I) (_ : forall (_ : R) (_ : R), R) (_ : bool) (_ : R), bigbody R I.

Parameter bigop :
  forall (R I : Type) (_ : R) (_ : list I) (_ : forall _ : I, bigbody R I), R.

Definition eqfun :=
  fun (A B : Type) (f g : forall _ : B, A) => forall x : B, @eq A (f x) (g x).

Definition pred := fun T : Type => forall _ : T, bool.

Section Defix.
Variables (T : Type) (n : nat) (f : forall _ : T, T) (x : T).
Fixpoint loop (m : nat) : T :=
  match m return T with
  | O => x
  | S i => f (loop i)
  end.
Definition iter := loop n.
End Defix.

Definition addn := nosimpl plus.
Definition subn := nosimpl minus.
Definition muln := nosimpl mult.

Fixpoint seq_iota (m n : nat) {struct n} : list nat :=
  match n return (list nat) with
  | O => @nil nat
  | S n' => @cons nat m (seq_iota (S m) n')
  end.

Definition index_iota := fun m n : nat => seq_iota m (subn n m).

Parameter eq_bigl :
  forall (R : Type) (idx : R) (op : forall (_ : R) (_ : R), R) (I : Type)
         (r : list I) (P1 P2 : pred I) (F : forall _ : I, R) (_ : @eqfun bool I P1 P2),
    @eq R (@bigop R I idx r (fun i : I => @BigBody R I i op (P1 i) (F i)))
        (@bigop R I idx r (fun i : I => @BigBody R I i op (P2 i) (F i))).

Parameter eq_big :
  forall (R : Type) (idx : R) (op : forall (_ : R) (_ : R), R) (I : Type)
         (r : list I) (P1 P2 : pred I) (F1 F2 : forall _ : I, R) (_ : @eqfun bool I P1 P2)
         (_ : forall (i : I) (_ : is_true (P1 i)), @eq R (F1 i) (F2 i)),
    @eq R (@bigop R I idx r (fun i : I => @BigBody R I i op (P1 i) (F1 i)))
        (@bigop R I idx r (fun i : I => @BigBody R I i op (P2 i) (F2 i))).

Parameter eq_bigr :
  forall (R : Type) (idx : R) (op : forall (_ : R) (_ : R), R) (I : Type)
         (r : list I) (P : pred I) (F1 F2 : forall _ : I, R)
         (_ : forall (i : I) (_ : is_true (P i)), @eq R (F1 i) (F2 i)),
    @eq R (@bigop R I idx r (fun i : I => @BigBody R I i op (P i) (F1 i)))
        (@bigop R I idx r (fun i : I => @BigBody R I i op (P i) (F2 i))).

Parameter big_const_nat :
  forall (R : Type) (idx : R) (op : forall (_ : R) (_ : R), R) (m n : nat) (x : R),
    @eq R (@bigop R nat idx (index_iota m n) (fun i : nat => @BigBody R nat i op true x))
        (@iter R (subn n m) (op x) idx).

Delimit Scope bool_scope with B.
Open Scope bool_scope.

Delimit Scope N_scope with num.
Delimit Scope nat_scope with N.

Delimit Scope big_scope with BIG.
Open Scope big_scope.

Reserved Notation "~~ b" (at level 35, right associativity).
Notation "~~ b" := (negb b) : bool_scope.

Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
  (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").
Reserved Notation "\big [ op / idx ]_ ( m <= i < n ) F"
  (at level 36, F at level 36, op, idx at level 10, i, m, n at level 50,
           format "'[' \big [ op / idx ]_ ( m  <=  i  <  n ) '/  '  F ']'").

Reserved Notation "\sum_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").

Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op P%B F))
     : big_scope.
Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (bigop idx (index_iota m n) (fun i : nat => BigBody i op true F))
     : big_scope.

Local Notation "+%N" := addn (at level 0, only parsing).

Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%N/0%N]_(m <= i < n | P%B) F%N) : nat_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%N/0%N]_(m <= i < n) F%N) : nat_scope.

Fixpoint odd n := if n is S n' then ~~ odd n' else false.

Parameter addnC : forall m n : nat, m + n = n + m.
Parameter mulnC : forall m n : nat, m * n = n * m.
Parameter addnA : forall x y z : nat, x + (y + z) = ((x + y) + z).
Parameter mulnA : forall x y z : nat, x * (y * z) = ((x * y) * z).

Parameter iter_addn_0 : forall m n : nat, @eq nat (@iter nat n (addn m) O) (muln m n).

Notation "x == y" := (Nat.eqb x y)
  (at level 70, no associativity) : bool_scope.
End Mocks.

Import Mocks.

(*****************************************************************************)

Lemma test_big_nested_1 (F G : nat -> nat) (m n : nat) :
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd (j * 1)) (i + j) =
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd j) (j + i).
Proof.
(* in interactive mode *)
under i Hi: eq_bigr.
  under j Hj: eq_big.
  { by rewrite mulnC /= addnC /= over. }
  { by rewrite addnC over. }
  over.
done.
Qed.

Lemma test_big_nested_2 (F G : nat -> nat) (m n : nat) :
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd (j * 1)) (i + j) =
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd j) (j + i).
Proof.
(* in one-liner mode *)
under i I: eq_bigr by under j J: eq_big by [rewrite mulnC /= addnC|rewrite addnC].
done.
Qed.

Lemma test_big_patt1 (F G : nat -> nat) (n : nat) :
  \sum_(0 <= i < n) (F i + G i) = \sum_(0 <= i < n) (G i + F i) + 0.
Proof.
under i Hi: [in RHS]eq_bigr.
  rewrite addnC.
  over.
done.
Qed.

Lemma test_big_patt2 (F G : nat -> nat) (n : nat) :
  \sum_(0 <= i < n) (F i + F i) =
  \sum_(0 <= i < n) 0 + \sum_(0 <= i < n) (F i * 2).
Proof.
under i Hi: [X in _ = _ + X]eq_bigr.
  (* the proof is not idiomatic as mathcomp lemmas are not available here *)
  rewrite mulnC /= addnA -plus_n_O.
  over.
by rewrite big_const_nat iter_addn_0.
Qed.

Lemma test_big_occs (F G : nat -> nat) (n : nat) :
  \sum_(0 <= i < n) (i * 0) = \sum_(0 <= i < n) (i * 0) + \sum_(0 <= i < n) (i * 0).
Proof.
under i Hi: {2}[in RHS]eq_bigr.
  by rewrite mulnC /= over.
by rewrite big_const_nat iter_addn_0.
Qed.

(* Solely used, one such renaming is useless in practice, but it works anyway *)
Lemma test_big_cosmetic (F G : nat -> nat) (m n : nat) :
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd (j * 1)) (i + j) =
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd j) (j + i).
Proof.
under a A: [RHS]eq_bigr by under b B: eq_bigr by []. (* renaming bound vars *)
simpl.
myadmit.
Qed.
