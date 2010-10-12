(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import List.
Require Import Peano_dec.
Require Import LegacyRing.
Require Import LegacyField_Compl.

Record Field_Theory : Type :=
  {A : Type;
   Aplus : A -> A -> A;
   Amult : A -> A -> A;
   Aone : A;
   Azero : A;
   Aopp : A -> A;
   Aeq : A -> A -> bool;
   Ainv : A -> A;
   Aminus : option (A -> A -> A);
   Adiv : option (A -> A -> A);
   RT : Ring_Theory Aplus Amult Aone Azero Aopp Aeq;
   Th_inv_def : forall n:A, n <> Azero -> Amult (Ainv n) n = Aone}.

(* The reflexion structure *)
Inductive ExprA : Set :=
  | EAzero : ExprA
  | EAone : ExprA
  | EAplus : ExprA -> ExprA -> ExprA
  | EAmult : ExprA -> ExprA -> ExprA
  | EAopp : ExprA -> ExprA
  | EAinv : ExprA -> ExprA
  | EAvar : nat -> ExprA.

(**** Decidability of equality ****)

Lemma eqExprA_O : forall e1 e2:ExprA, {e1 = e2} + {e1 <> e2}.
Proof.
  double induction e1 e2; try intros;
   try (left; reflexivity) || (try (right; discriminate)).
  elim (H1 e0); intro y; elim (H2 e); intro y0;
   try
    (left; rewrite y; rewrite y0; auto) ||
      (right; red in |- *; intro; inversion H3; auto).
  elim (H1 e0); intro y; elim (H2 e); intro y0;
   try
    (left; rewrite y; rewrite y0; auto) ||
      (right; red in |- *; intro; inversion H3; auto).
  elim (H0 e); intro y.
  left; rewrite y; auto.
  right; red in |- *; intro; inversion H1; auto.
  elim (H0 e); intro y.
  left; rewrite y; auto.
  right; red in |- *; intro; inversion H1; auto.
  elim (eq_nat_dec n n0); intro y.
  left; rewrite y; auto.
  right; red in |- *; intro; inversion H; auto.
Defined.

Definition eq_nat_dec := Eval compute in eq_nat_dec.
Definition eqExprA := Eval compute in eqExprA_O.

(**** Generation of the multiplier ****)

Fixpoint mult_of_list (e:list ExprA) : ExprA :=
  match e with
  | nil => EAone
  | e1 :: l1 => EAmult e1 (mult_of_list l1)
  end.

Section Theory_of_fields.

Variable T : Field_Theory.

Let AT := A T.
Let AplusT := Aplus T.
Let AmultT := Amult T.
Let AoneT := Aone T.
Let AzeroT := Azero T.
Let AoppT := Aopp T.
Let AeqT := Aeq T.
Let AinvT := Ainv T.
Let RTT := RT T.
Let Th_inv_defT := Th_inv_def T.

Add Legacy Abstract Ring (A T) (Aplus T) (Amult T) (Aone T) (
 Azero T) (Aopp T) (Aeq T) (RT T).

Add Legacy Abstract Ring AT AplusT AmultT AoneT AzeroT AoppT AeqT RTT.

(***************************)
(*    Lemmas to be used    *)
(***************************)

Lemma AplusT_comm : forall r1 r2:AT, AplusT r1 r2 = AplusT r2 r1.
Proof.
  intros; legacy ring.
Qed.

Lemma AplusT_assoc :
 forall r1 r2 r3:AT, AplusT (AplusT r1 r2) r3 = AplusT r1 (AplusT r2 r3).
Proof.
  intros; legacy ring.
Qed.

Lemma AmultT_comm : forall r1 r2:AT, AmultT r1 r2 = AmultT r2 r1.
Proof.
  intros; legacy ring.
Qed.

Lemma AmultT_assoc :
 forall r1 r2 r3:AT, AmultT (AmultT r1 r2) r3 = AmultT r1 (AmultT r2 r3).
Proof.
  intros; legacy ring.
Qed.

Lemma AplusT_Ol : forall r:AT, AplusT AzeroT r = r.
Proof.
  intros; legacy ring.
Qed.

Lemma AmultT_1l : forall r:AT, AmultT AoneT r = r.
Proof.
  intros; legacy ring.
Qed.

Lemma AplusT_AoppT_r : forall r:AT, AplusT r (AoppT r) = AzeroT.
Proof.
  intros; legacy ring.
Qed.

Lemma AmultT_AplusT_distr :
 forall r1 r2 r3:AT,
   AmultT r1 (AplusT r2 r3) = AplusT (AmultT r1 r2) (AmultT r1 r3).
Proof.
  intros; legacy ring.
Qed.

Lemma r_AplusT_plus : forall r r1 r2:AT, AplusT r r1 = AplusT r r2 -> r1 = r2.
Proof.
  intros; transitivity (AplusT (AplusT (AoppT r) r) r1).
  legacy ring.
  transitivity (AplusT (AplusT (AoppT r) r) r2).
  repeat rewrite AplusT_assoc; rewrite <- H; reflexivity.
  legacy ring.
Qed.

Lemma r_AmultT_mult :
 forall r r1 r2:AT, AmultT r r1 = AmultT r r2 -> r <> AzeroT -> r1 = r2.
Proof.
  intros; transitivity (AmultT (AmultT (AinvT r) r) r1).
  rewrite Th_inv_defT; [ symmetry  in |- *; apply AmultT_1l; auto | auto ].
  transitivity (AmultT (AmultT (AinvT r) r) r2).
  repeat rewrite AmultT_assoc; rewrite H; trivial.
  rewrite Th_inv_defT; [ apply AmultT_1l; auto | auto ].
Qed.

Lemma AmultT_Or : forall r:AT, AmultT r AzeroT = AzeroT.
Proof.
  intro; legacy ring.
Qed.

Lemma AmultT_Ol : forall r:AT, AmultT AzeroT r = AzeroT.
Proof.
  intro; legacy ring.
Qed.

Lemma AmultT_1r : forall r:AT, AmultT r AoneT = r.
Proof.
  intro; legacy ring.
Qed.

Lemma AinvT_r : forall r:AT, r <> AzeroT -> AmultT r (AinvT r) = AoneT.
Proof.
  intros; rewrite AmultT_comm; apply Th_inv_defT; auto.
Qed.

Lemma Rmult_neq_0_reg :
 forall r1 r2:AT, AmultT r1 r2 <> AzeroT -> r1 <> AzeroT /\ r2 <> AzeroT.
Proof.
  intros r1 r2 H; split; red in |- *; intro; apply H; rewrite H0; legacy ring.
Qed.

(************************)
(*    Interpretation    *)
(************************)

(**** ExprA --> A ****)

Fixpoint interp_ExprA (lvar:list (AT * nat)) (e:ExprA) {struct e} :
 AT :=
  match e with
  | EAzero => AzeroT
  | EAone => AoneT
  | EAplus e1 e2 => AplusT (interp_ExprA lvar e1) (interp_ExprA lvar e2)
  | EAmult e1 e2 => AmultT (interp_ExprA lvar e1) (interp_ExprA lvar e2)
  | EAopp e => Aopp T (interp_ExprA lvar e)
  | EAinv e => Ainv T (interp_ExprA lvar e)
  | EAvar n => assoc_2nd AT nat eq_nat_dec lvar n AzeroT
  end.

(************************)
(*    Simplification    *)
(************************)

(**** Associativity ****)

Definition merge_mult :=
  (fix merge_mult (e1:ExprA) : ExprA -> ExprA :=
     fun e2:ExprA =>
       match e1 with
       | EAmult t1 t2 =>
           match t2 with
           | EAmult t2 t3 => EAmult t1 (EAmult t2 (merge_mult t3 e2))
           | _ => EAmult t1 (EAmult t2 e2)
           end
       | _ => EAmult e1 e2
       end).

Fixpoint assoc_mult (e:ExprA) : ExprA :=
  match e with
  | EAmult e1 e3 =>
      match e1 with
      | EAmult e1 e2 =>
          merge_mult (merge_mult (assoc_mult e1) (assoc_mult e2))
            (assoc_mult e3)
      | _ => EAmult e1 (assoc_mult e3)
      end
  | _ => e
  end.

Definition merge_plus :=
  (fix merge_plus (e1:ExprA) : ExprA -> ExprA :=
     fun e2:ExprA =>
       match e1 with
       | EAplus t1 t2 =>
           match t2 with
           | EAplus t2 t3 => EAplus t1 (EAplus t2 (merge_plus t3 e2))
           | _ => EAplus t1 (EAplus t2 e2)
           end
       | _ => EAplus e1 e2
       end).

Fixpoint assoc (e:ExprA) : ExprA :=
  match e with
  | EAplus e1 e3 =>
      match e1 with
      | EAplus e1 e2 =>
          merge_plus (merge_plus (assoc e1) (assoc e2)) (assoc e3)
      | _ => EAplus (assoc_mult e1) (assoc e3)
      end
  | _ => assoc_mult e
  end.

Lemma merge_mult_correct1 :
 forall (e1 e2 e3:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (merge_mult (EAmult e1 e2) e3) =
   interp_ExprA lvar (EAmult e1 (merge_mult e2 e3)).
Proof.
intros e1 e2; generalize e1; generalize e2; clear e1 e2.
simple induction e2; auto; intros.
unfold merge_mult at 1 in |- *; fold merge_mult in |- *;
 unfold interp_ExprA at 2 in |- *; fold interp_ExprA in |- *;
 rewrite (H0 e e3 lvar); unfold interp_ExprA at 1 in |- *;
 fold interp_ExprA in |- *; unfold interp_ExprA at 5 in |- *;
 fold interp_ExprA in |- *; auto.
Qed.

Lemma merge_mult_correct :
 forall (e1 e2:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (merge_mult e1 e2) = interp_ExprA lvar (EAmult e1 e2).
Proof.
simple induction e1; auto; intros.
elim e0; try (intros; simpl in |- *; legacy ring).
unfold interp_ExprA in H2; fold interp_ExprA in H2;
 cut
  (AmultT (interp_ExprA lvar e2)
     (AmultT (interp_ExprA lvar e4)
        (AmultT (interp_ExprA lvar e) (interp_ExprA lvar e3))) =
   AmultT
     (AmultT (AmultT (interp_ExprA lvar e) (interp_ExprA lvar e4))
        (interp_ExprA lvar e2)) (interp_ExprA lvar e3)).
intro H3; rewrite H3; rewrite <- H2; rewrite merge_mult_correct1;
 simpl in |- *; legacy ring.
legacy ring.
Qed.

Lemma assoc_mult_correct1 :
 forall (e1 e2:ExprA) (lvar:list (AT * nat)),
   AmultT (interp_ExprA lvar (assoc_mult e1))
     (interp_ExprA lvar (assoc_mult e2)) =
   interp_ExprA lvar (assoc_mult (EAmult e1 e2)).
Proof.
simple induction e1; auto; intros.
rewrite <- (H e0 lvar); simpl in |- *; rewrite merge_mult_correct;
 simpl in |- *; rewrite merge_mult_correct; simpl in |- *;
 auto.
Qed.

Lemma assoc_mult_correct :
 forall (e:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (assoc_mult e) = interp_ExprA lvar e.
Proof.
simple induction e; auto; intros.
elim e0; intros.
intros; simpl in |- *; legacy ring.
simpl in |- *; rewrite (AmultT_1l (interp_ExprA lvar (assoc_mult e1)));
 rewrite (AmultT_1l (interp_ExprA lvar e1)); apply H0.
simpl in |- *; rewrite (H0 lvar); auto.
simpl in |- *; rewrite merge_mult_correct; simpl in |- *;
 rewrite merge_mult_correct; simpl in |- *; rewrite AmultT_assoc;
 rewrite assoc_mult_correct1; rewrite H2; simpl in |- *;
 rewrite <- assoc_mult_correct1 in H1; unfold interp_ExprA at 3 in H1;
 fold interp_ExprA in H1; rewrite (H0 lvar) in H1;
 rewrite (AmultT_comm (interp_ExprA lvar e3) (interp_ExprA lvar e1));
 rewrite <- AmultT_assoc; rewrite H1; rewrite AmultT_assoc;
 legacy ring.
simpl in |- *; rewrite (H0 lvar); auto.
simpl in |- *; rewrite (H0 lvar); auto.
simpl in |- *; rewrite (H0 lvar); auto.
Qed.

Lemma merge_plus_correct1 :
 forall (e1 e2 e3:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (merge_plus (EAplus e1 e2) e3) =
   interp_ExprA lvar (EAplus e1 (merge_plus e2 e3)).
Proof.
intros e1 e2; generalize e1; generalize e2; clear e1 e2.
simple induction e2; auto; intros.
unfold merge_plus at 1 in |- *; fold merge_plus in |- *;
 unfold interp_ExprA at 2 in |- *; fold interp_ExprA in |- *;
 rewrite (H0 e e3 lvar); unfold interp_ExprA at 1 in |- *;
 fold interp_ExprA in |- *; unfold interp_ExprA at 5 in |- *;
 fold interp_ExprA in |- *; auto.
Qed.

Lemma merge_plus_correct :
 forall (e1 e2:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (merge_plus e1 e2) = interp_ExprA lvar (EAplus e1 e2).
Proof.
simple induction e1; auto; intros.
elim e0; try intros; try (simpl in |- *; legacy ring).
unfold interp_ExprA in H2; fold interp_ExprA in H2;
 cut
  (AplusT (interp_ExprA lvar e2)
     (AplusT (interp_ExprA lvar e4)
        (AplusT (interp_ExprA lvar e) (interp_ExprA lvar e3))) =
   AplusT
     (AplusT (AplusT (interp_ExprA lvar e) (interp_ExprA lvar e4))
        (interp_ExprA lvar e2)) (interp_ExprA lvar e3)).
intro H3; rewrite H3; rewrite <- H2; rewrite merge_plus_correct1;
 simpl in |- *; legacy ring.
legacy ring.
Qed.

Lemma assoc_plus_correct :
 forall (e1 e2:ExprA) (lvar:list (AT * nat)),
   AplusT (interp_ExprA lvar (assoc e1)) (interp_ExprA lvar (assoc e2)) =
   interp_ExprA lvar (assoc (EAplus e1 e2)).
Proof.
simple induction e1; auto; intros.
rewrite <- (H e0 lvar); simpl in |- *; rewrite merge_plus_correct;
 simpl in |- *; rewrite merge_plus_correct; simpl in |- *;
 auto.
Qed.

Lemma assoc_correct :
 forall (e:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (assoc e) = interp_ExprA lvar e.
Proof.
simple induction e; auto; intros.
elim e0; intros.
simpl in |- *; rewrite (H0 lvar); auto.
simpl in |- *; rewrite (H0 lvar); auto.
simpl in |- *; rewrite merge_plus_correct; simpl in |- *;
 rewrite merge_plus_correct; simpl in |- *; rewrite AplusT_assoc;
 rewrite assoc_plus_correct; rewrite H2; simpl in |- *;
 apply
  (r_AplusT_plus (interp_ExprA lvar (assoc e1))
     (AplusT (interp_ExprA lvar (assoc e2))
        (AplusT (interp_ExprA lvar e3) (interp_ExprA lvar e1)))
     (AplusT (AplusT (interp_ExprA lvar e2) (interp_ExprA lvar e3))
        (interp_ExprA lvar e1))); rewrite <- AplusT_assoc;
 rewrite
  (AplusT_comm (interp_ExprA lvar (assoc e1)) (interp_ExprA lvar (assoc e2)))
  ; rewrite assoc_plus_correct; rewrite H1; simpl in |- *;
 rewrite (H0 lvar);
 rewrite <-
  (AplusT_assoc (AplusT (interp_ExprA lvar e2) (interp_ExprA lvar e1))
     (interp_ExprA lvar e3) (interp_ExprA lvar e1))
  ;
 rewrite
  (AplusT_assoc (interp_ExprA lvar e2) (interp_ExprA lvar e1)
     (interp_ExprA lvar e3));
 rewrite (AplusT_comm (interp_ExprA lvar e1) (interp_ExprA lvar e3));
 rewrite <-
  (AplusT_assoc (interp_ExprA lvar e2) (interp_ExprA lvar e3)
     (interp_ExprA lvar e1)); apply AplusT_comm.
unfold assoc in |- *; fold assoc in |- *; unfold interp_ExprA in |- *;
 fold interp_ExprA in |- *; rewrite assoc_mult_correct;
 rewrite (H0 lvar); simpl in |- *; auto.
simpl in |- *; rewrite (H0 lvar); auto.
simpl in |- *; rewrite (H0 lvar); auto.
simpl in |- *; rewrite (H0 lvar); auto.
unfold assoc in |- *; fold assoc in |- *; unfold interp_ExprA in |- *;
 fold interp_ExprA in |- *; rewrite assoc_mult_correct;
 simpl in |- *; auto.
Qed.

(**** Distribution *****)

Fixpoint distrib_EAopp (e:ExprA) : ExprA :=
  match e with
  | EAplus e1 e2 => EAplus (distrib_EAopp e1) (distrib_EAopp e2)
  | EAmult e1 e2 => EAmult (distrib_EAopp e1) (distrib_EAopp e2)
  | EAopp e => EAmult (EAopp EAone) (distrib_EAopp e)
  | e => e
  end.

Definition distrib_mult_right :=
  (fix distrib_mult_right (e1:ExprA) : ExprA -> ExprA :=
     fun e2:ExprA =>
       match e1 with
       | EAplus t1 t2 =>
           EAplus (distrib_mult_right t1 e2) (distrib_mult_right t2 e2)
       | _ => EAmult e1 e2
       end).

Fixpoint distrib_mult_left (e1 e2:ExprA) {struct e1} : ExprA :=
  match e1 with
  | EAplus t1 t2 =>
      EAplus (distrib_mult_left t1 e2) (distrib_mult_left t2 e2)
  | _ => distrib_mult_right e2 e1
  end.

Fixpoint distrib_main (e:ExprA) : ExprA :=
  match e with
  | EAmult e1 e2 => distrib_mult_left (distrib_main e1) (distrib_main e2)
  | EAplus e1 e2 => EAplus (distrib_main e1) (distrib_main e2)
  | EAopp e => EAopp (distrib_main e)
  | _ => e
  end.

Definition distrib (e:ExprA) : ExprA := distrib_main (distrib_EAopp e).

Lemma distrib_mult_right_correct :
 forall (e1 e2:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (distrib_mult_right e1 e2) =
   AmultT (interp_ExprA lvar e1) (interp_ExprA lvar e2).
Proof.
simple induction e1; try intros; simpl in |- *; auto.
rewrite AmultT_comm; rewrite AmultT_AplusT_distr; rewrite (H e2 lvar);
 rewrite (H0 e2 lvar); legacy ring.
Qed.

Lemma distrib_mult_left_correct :
 forall (e1 e2:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (distrib_mult_left e1 e2) =
   AmultT (interp_ExprA lvar e1) (interp_ExprA lvar e2).
Proof.
simple induction e1; try intros; simpl in |- *.
rewrite AmultT_Ol; rewrite distrib_mult_right_correct; simpl in |- *;
 apply AmultT_Or.
rewrite distrib_mult_right_correct; simpl in |- *; apply AmultT_comm.
rewrite AmultT_comm;
 rewrite
  (AmultT_AplusT_distr (interp_ExprA lvar e2) (interp_ExprA lvar e)
     (interp_ExprA lvar e0));
 rewrite (AmultT_comm (interp_ExprA lvar e2) (interp_ExprA lvar e));
 rewrite (AmultT_comm (interp_ExprA lvar e2) (interp_ExprA lvar e0));
 rewrite (H e2 lvar); rewrite (H0 e2 lvar); auto.
rewrite distrib_mult_right_correct; simpl in |- *; apply AmultT_comm.
rewrite distrib_mult_right_correct; simpl in |- *; apply AmultT_comm.
rewrite distrib_mult_right_correct; simpl in |- *; apply AmultT_comm.
rewrite distrib_mult_right_correct; simpl in |- *; apply AmultT_comm.
Qed.

Lemma distrib_correct :
 forall (e:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (distrib e) = interp_ExprA lvar e.
Proof.
simple induction e; intros; auto.
simpl in |- *; rewrite <- (H lvar); rewrite <- (H0 lvar);
 unfold distrib in |- *; simpl in |- *; auto.
simpl in |- *; rewrite <- (H lvar); rewrite <- (H0 lvar);
 unfold distrib in |- *; simpl in |- *; apply distrib_mult_left_correct.
simpl in |- *; fold AoppT in |- *; rewrite <- (H lvar);
 unfold distrib in |- *; simpl in |- *; rewrite distrib_mult_right_correct;
 simpl in |- *; fold AoppT in |- *; legacy ring.
Qed.

(**** Multiplication by the inverse product ****)

Lemma mult_eq :
 forall (e1 e2 a:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar a <> AzeroT ->
   interp_ExprA lvar (EAmult a e1) = interp_ExprA lvar (EAmult a e2) ->
   interp_ExprA lvar e1 = interp_ExprA lvar e2.
Proof.
  simpl in |- *; intros;
   apply
    (r_AmultT_mult (interp_ExprA lvar a) (interp_ExprA lvar e1)
       (interp_ExprA lvar e2)); assumption.
Qed.

Fixpoint multiply_aux (a e:ExprA) {struct e} : ExprA :=
  match e with
  | EAplus e1 e2 => EAplus (EAmult a e1) (multiply_aux a e2)
  | _ => EAmult a e
  end.

Definition multiply (e:ExprA) : ExprA :=
  match e with
  | EAmult a e1 => multiply_aux a e1
  | _ => e
  end.

Lemma multiply_aux_correct :
 forall (a e:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (multiply_aux a e) =
   AmultT (interp_ExprA lvar a) (interp_ExprA lvar e).
Proof.
simple induction e; simpl in |- *; intros; try rewrite merge_mult_correct;
 auto.
  simpl in |- *; rewrite (H0 lvar); legacy ring.
Qed.

Lemma multiply_correct :
 forall (e:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar (multiply e) = interp_ExprA lvar e.
Proof.
  simple induction e; simpl in |- *; auto.
  intros; apply multiply_aux_correct.
Qed.

(**** Permutations and simplification ****)

Fixpoint monom_remove (a m:ExprA) {struct m} : ExprA :=
  match m with
  | EAmult m0 m1 =>
      match eqExprA m0 (EAinv a) with
      | left _ => m1
      | right _ => EAmult m0 (monom_remove a m1)
      end
  | _ =>
      match eqExprA m (EAinv a) with
      | left _ => EAone
      | right _ => EAmult a m
      end
  end.

Definition monom_simplif_rem :=
  (fix monom_simplif_rem (a:ExprA) : ExprA -> ExprA :=
     fun m:ExprA =>
       match a with
       | EAmult a0 a1 => monom_simplif_rem a1 (monom_remove a0 m)
       | _ => monom_remove a m
       end).

Definition monom_simplif (a m:ExprA) : ExprA :=
  match m with
  | EAmult a' m' =>
      match eqExprA a a' with
      | left _ => monom_simplif_rem a m'
      | right _ => m
      end
  | _ => m
  end.

Fixpoint inverse_simplif (a e:ExprA) {struct e} : ExprA :=
  match e with
  | EAplus e1 e2 => EAplus (monom_simplif a e1) (inverse_simplif a e2)
  | _ => monom_simplif a e
  end.

Lemma monom_remove_correct :
 forall (e a:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar a <> AzeroT ->
   interp_ExprA lvar (monom_remove a e) =
   AmultT (interp_ExprA lvar a) (interp_ExprA lvar e).
Proof.
simple induction e; intros.
simpl in |- *; case (eqExprA EAzero (EAinv a)); intros;
 [ inversion e0 | simpl in |- *; trivial ].
simpl in |- *; case (eqExprA EAone (EAinv a)); intros;
 [ inversion e0 | simpl in |- *; trivial ].
simpl in |- *; case (eqExprA (EAplus e0 e1) (EAinv a)); intros;
 [ inversion e2 | simpl in |- *; trivial ].
simpl in |- *; case (eqExprA e0 (EAinv a)); intros.
rewrite e2; simpl in |- *; fold AinvT in |- *.
rewrite <-
 (AmultT_assoc (interp_ExprA lvar a) (AinvT (interp_ExprA lvar a))
    (interp_ExprA lvar e1)); rewrite AinvT_r; [ legacy ring | assumption ].
simpl in |- *; rewrite H0; auto; legacy ring.
simpl in |- *; fold AoppT in |- *; case (eqExprA (EAopp e0) (EAinv a));
 intros; [ inversion e1 | simpl in |- *; trivial ].
unfold monom_remove in |- *; case (eqExprA (EAinv e0) (EAinv a)); intros.
case (eqExprA e0 a); intros.
rewrite e2; simpl in |- *; fold AinvT in |- *; rewrite AinvT_r; auto.
inversion e1; simpl in |- *; exfalso; auto.
simpl in |- *; trivial.
unfold monom_remove in |- *; case (eqExprA (EAvar n) (EAinv a)); intros;
 [ inversion e0 | simpl in |- *; trivial ].
Qed.

Lemma monom_simplif_rem_correct :
 forall (a e:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar a <> AzeroT ->
   interp_ExprA lvar (monom_simplif_rem a e) =
   AmultT (interp_ExprA lvar a) (interp_ExprA lvar e).
Proof.
simple induction a; simpl in |- *; intros; try rewrite monom_remove_correct;
 auto.
elim (Rmult_neq_0_reg (interp_ExprA lvar e) (interp_ExprA lvar e0) H1);
 intros.
rewrite (H0 (monom_remove e e1) lvar H3); rewrite monom_remove_correct; auto.
legacy ring.
Qed.

Lemma monom_simplif_correct :
 forall (e a:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar a <> AzeroT ->
   interp_ExprA lvar (monom_simplif a e) = interp_ExprA lvar e.
Proof.
simple induction e; intros; auto.
simpl in |- *; case (eqExprA a e0); intros.
rewrite <- e2; apply monom_simplif_rem_correct; auto.
simpl in |- *; trivial.
Qed.

Lemma inverse_correct :
 forall (e a:ExprA) (lvar:list (AT * nat)),
   interp_ExprA lvar a <> AzeroT ->
   interp_ExprA lvar (inverse_simplif a e) = interp_ExprA lvar e.
Proof.
simple induction e; intros; auto.
simpl in |- *; rewrite (H0 a lvar H1); rewrite monom_simplif_correct; auto.
unfold inverse_simplif in |- *; rewrite monom_simplif_correct; auto.
Qed.

End Theory_of_fields.

(* Compatibility *)
Notation AplusT_sym := AplusT_comm (only parsing).
Notation AmultT_sym := AmultT_comm (only parsing).
