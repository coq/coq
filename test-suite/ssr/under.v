Require Import ssreflect.
Require Import ssrbool TestSuite.ssr_mini_mathcomp.
Global Unset SsrOldRewriteGoalsOrder.

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

Definition eqfun :=
  fun (A B : Type) (f g : forall _ : B, A) => forall x : B, @eq A (f x) (g x).

Section Defix.
Variables (T : Type) (n : nat) (f : forall _ : T, T) (x : T).
Fixpoint loop (m : nat) : T :=
  match m return T with
  | O => x
  | S i => f (loop i)
  end.
Definition iter := loop n.
End Defix.

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

Delimit Scope N_scope with num.
Delimit Scope nat_scope with N.

Reserved Notation "\sum_ ( m <= i < n | P ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n  |  P ) '/  '  F ']'").
Reserved Notation "\sum_ ( m <= i < n ) F"
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").

Local Notation "+%N" := addn (at level 0, only parsing).

Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%N/0%N]_(m <= i < n | P%B) F%N) : (*nat_scope*) big_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%N/0%N]_(m <= i < n) F%N) : (*nat_scope*) big_scope.

Parameter iter_addn_0 : forall m n : nat, @eq nat (@iter nat n (addn m) O) (muln m n).

End Mocks.

Import Mocks.

(*****************************************************************************)

Lemma test_big_nested_1 (F G : nat -> nat) (m n : nat) :
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd (j * 1)) (i + j) =
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd j) (j + i).
Proof.
(* in interactive mode *)
under eq_bigr => i Hi.
  under eq_big => [j|j Hj].
  { rewrite muln1. over. }
  { rewrite addnC. over. }
  simpl. (* or: cbv beta. *)
  over.
by [].
Qed.

Lemma test_big_nested_2 (F G : nat -> nat) (m n : nat) :
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd (j * 1)) (i + j) =
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd j) (j + i).
Proof.
(* in one-liner mode *)
under eq_bigr => i Hi do under eq_big => [j|j Hj] do [rewrite muln1 | rewrite addnC ].
done.
Qed.

Lemma test_big_2cond_0intro (F : nat -> nat) (m : nat) :
  \sum_(0 <= i < m | odd (i + 1)) (i + 2) >= 0.
Proof.
(* in interactive mode *)
under eq_big.
{ move=> n; rewrite (addnC n 1); over. }
{ move=> i Hi; rewrite (addnC i 2); over. }
done.
Qed.

Lemma test_big_2cond_1intro (F : nat -> nat) (m : nat) :
  \sum_(0 <= i < m | odd (i + 1)) (i + 2) >= 0.
Proof.
(* in interactive mode *)
Fail under eq_big => i.
(* as it amounts to [under eq_big => [i]] *)
Abort.

Lemma test_big_2cond_all (F : nat -> nat) (m : nat) :
  \sum_(0 <= i < m | odd (i + 1)) (i + 2) >= 0.
Proof.
(* in interactive mode *)
Fail under eq_big => *.
(* as it amounts to [under eq_big => [*]] *)
Abort.

Lemma test_big_2cond_all_implied (F : nat -> nat) (m : nat) :
  \sum_(0 <= i < m | odd (i + 1)) (i + 2) >= 0.
Proof.
(* in one-liner mode *)
under eq_big do [rewrite addnC
                |rewrite addnC].
(* amounts to [under eq_big => [*|*] do [...|...]] *)
done.
Qed.

Lemma test_big_patt1 (F G : nat -> nat) (n : nat) :
  \sum_(0 <= i < n) (F i + G i) = \sum_(0 <= i < n) (G i + F i) + 0.
Proof.
under [in RHS]eq_bigr => i Hi.
  by rewrite addnC over.
done.
Qed.

Lemma test_big_patt2 (F G : nat -> nat) (n : nat) :
  \sum_(0 <= i < n) (F i + F i) =
  \sum_(0 <= i < n) 0 + \sum_(0 <= i < n) (F i * 2).
Proof.
under [X in _ = _ + X]eq_bigr => i Hi do rewrite mulnS muln1.
by rewrite big_const_nat iter_addn_0.
Qed.

Lemma test_big_occs (F G : nat -> nat) (n : nat) :
  \sum_(0 <= i < n) (i * 0) = \sum_(0 <= i < n) (i * 0) + \sum_(0 <= i < n) (i * 0).
Proof.
under {2}[in RHS]eq_bigr => i Hi do rewrite muln0.
by rewrite big_const_nat iter_addn_0 mul0n addn0.
Qed.

Lemma test_big_occs_inH (F G : nat -> nat) (n : nat) :
  \sum_(0 <= i < n) (i * 0) = \sum_(0 <= i < n) (i * 0) + \sum_(0 <= i < n) (i * 0) -> True.
Proof.
move=> H.
do [under {2}[in RHS]eq_bigr => i Hi do rewrite muln0] in H.
by rewrite big_const_nat iter_addn_0 mul0n addn0 in H.
Qed.

(* Solely used, one such renaming is useless in practice, but it works anyway *)
Lemma test_big_cosmetic (F G : nat -> nat) (m n : nat) :
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd (j * 1)) (i + j) =
  \sum_(0 <= i < m) \sum_(0 <= j < n | odd j) (j + i).
Proof.
under [RHS]eq_bigr => a A do under eq_bigr => b B do []. (* renaming bound vars *)
myadmit.
Qed.

Lemma test_big_andb (F : nat -> nat) (m n : nat) :
  \sum_(0 <= i < 5 | odd i && (i == 1)) i = 1.
Proof.
under eq_bigl => i do [rewrite andb_idl; first by move/eqP->].
under eq_bigr => i do move/eqP=>{1}->. (* the 2nd occ should not be touched *)
myadmit.
Qed.

Lemma test_foo (f1 f2 : nat -> nat) (f_eq : forall n, f1 n = f2 n)
      (G : (nat -> nat) -> nat)
      (Lem : forall f1 f2 : nat -> nat,
          True ->
          (forall n, f1 n = f2 n) ->
          False = False ->
          G f1 = G f2) :
  G f1 = G f2.
Proof.
(*
under x: Lem.
- done.
- rewrite f_eq; over.
- done.
 *)
under Lem => [|x|] do [done|rewrite f_eq|done].
done.
Qed.


(* Inspired From Coquelicot.Lub. *)
(* http://coquelicot.saclay.inria.fr/html/Coquelicot.Lub.html#Lub_Rbar_eqset *)

Parameters (R Rbar : Set) (R0 : R) (Rbar0 : Rbar).
Parameter Rbar_le : Rbar -> Rbar -> Prop.
Parameter Lub_Rbar : (R -> Prop) -> Rbar.
Parameter Lub_Rbar_eqset :
  forall E1 E2 : R -> Prop,
    (forall x : R, E1 x <-> E2 x) ->
    Lub_Rbar E1 = Lub_Rbar E2.

Lemma test_Lub_Rbar (E : R -> Prop)  :
  Rbar_le Rbar0 (Lub_Rbar (fun x => x = R0 \/ E x)).
Proof.
under Lub_Rbar_eqset => r.
by rewrite over.
Abort.

Lemma ex_iff R (P1 P2 : R -> Prop) :
  (forall x : R, P1 x <-> P2 x) -> ((exists x, P1 x) <-> (exists x, P2 x)).
Proof.
by move=> H; split; move=> [x Hx]; exists x; apply H.
Qed.

Arguments ex_iff [R P1] P2 iffP12.

(** Load the [setoid_rewrite] machinery *)
Require Setoid.

(** Replay the tactics from [test_Lub_Rbar] in this new environment *)
Lemma test_Lub_Rbar_again (E : R -> Prop)  :
  Rbar_le Rbar0 (Lub_Rbar (fun x => x = R0 \/ E x)).
Proof.
under Lub_Rbar_eqset => r.
by rewrite over.
Abort.

Lemma test_ex_iff (P : nat -> Prop) : (exists x, P x) -> True.
under ex_iff => n. (* this requires [Setoid] *)
by rewrite over.
by move=> _.
Qed.

Section TestGeneric.
Context {A B : Type} {R : nat -> B -> B -> Prop}
        `{!forall n : nat, RelationClasses.Equivalence (R n)}.
Variables (F : (A -> A -> B) -> B).
Hypothesis ex_gen : forall (n : nat) (P1 P2 : A -> A -> B),
  (forall x y : A, R n (P1 x y) (P2 x y)) -> (R n (F P1) (F P2)).
Arguments ex_gen [n P1] P2 relP12.
Lemma test_ex_gen (P1 P2 : A -> A -> B) (n : nat) :
  (forall x y : A, P2 x y = P2 y x) ->
  R n (F P1) (F P2) /\ True -> True.
Proof.
move=> P2C.
under [X in R _ _ X]ex_gen => a b.
  by rewrite P2C over.
by move => _.
Qed.
End TestGeneric.

Import Setoid.
(* to expose [Coq.Relations.Relation_Definitions.reflexive],
   [Coq.Classes.RelationClasses.RewriteRelation], and so on. *)

Section TestGeneric2.
(* Some toy abstract example with a parameterized setoid type *)
Record Setoid (m n : nat) : Type :=
  { car : Type
  ; Rel : car -> car -> Prop
  ; refl : reflexive _ Rel
  ; sym : symmetric _ Rel
  ; trans : transitive _ Rel
  }.

Context {m n : nat}.
Add Parametric Relation (s : Setoid m n) : (car s) (@Rel _ _ s)
  reflexivity proved by (@refl _ _ s)
  symmetry proved by (@sym _ _ s)
  transitivity proved by (@trans _ _ s)
  as eq_rel.

Context {A : Type} {s1 s2 : Setoid m n}.

Let B := @car m n s1.
Let C := @car m n s2.
Variable (F : C -> (A -> A -> B) -> C).
Hypothesis rel2_gen :
  forall (c1 c2 : C) (P1 P2 : A -> A -> B),
    Rel c1 c2 ->
    (forall a b : A, Rel (P1 a b) (P2 a b)) ->
    Rel (F c1 P1) (F c2 P2).
Arguments rel2_gen [c1] c2 [P1] P2 relc12 relP12.
Lemma test_rel2_gen (c : C) (P : A -> A -> B)
  (toy_hyp : forall a b, P a b = P b a) :
  Rel (F c P) (F c (fun a b => P b a)).
Proof.
under [here in Rel _ here]rel2_gen.
- over.
- by move=> a b; rewrite toy_hyp over.
- reflexivity.
Qed.
End TestGeneric2.
