
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Export ZArith.
Open Local Scope Z_scope.

Coercion Zpos : positive >-> Z.
Coercion Z_of_N : N >-> Z.

Lemma Zpos_plus : forall p q, Zpos (p + q) = p + q.
Proof. intros;trivial. Qed.

Lemma Zpos_mult : forall p q, Zpos (p * q) = p * q.
Proof. intros;trivial. Qed.

Lemma Zpos_xI_add : forall p, Zpos (xI p) = Zpos p + Zpos p + Zpos 1.
Proof. intros p;rewrite Zpos_xI;ring. Qed.

Lemma Zpos_xO_add : forall p, Zpos (xO p) = Zpos p + Zpos p.
Proof. intros p;rewrite Zpos_xO;ring. Qed.

Lemma Psucc_Zplus : forall p, Zpos (Psucc p) = p + 1.
Proof. intros p;rewrite Zpos_succ_morphism;unfold Zsucc;trivial. Qed.

Hint Rewrite Zpos_xI_add Zpos_xO_add Pplus_carry_spec 
 Psucc_Zplus Zpos_plus : zmisc.

Lemma Zlt_0_pos : forall p, 0 < Zpos p.
Proof. unfold Zlt;trivial. Qed.
  

Lemma Pminus_mask_carry_spec : forall p q, 
  Pminus_mask_carry p q = Pminus_mask p (Psucc q).
Proof.
 intros p q;generalize q p;clear q p.
 induction q;destruct p;simpl;try rewrite IHq;trivial.
 destruct p;trivial.  destruct p;trivial.
Qed.

Hint Rewrite Pminus_mask_carry_spec : zmisc.

Ltac zsimpl := autorewrite with zmisc.
Ltac CaseEq t := generalize (refl_equal t);pattern t at -1;case t.
Ltac generalizeclear H := generalize H;clear H.

Lemma Pminus_mask_spec : 
   forall p q, 
    match Pminus_mask p q with
    | IsNul    => Zpos p =  Zpos q
    | IsPos k => Zpos p = q + k 
    | IsNeq   => p < q
    end.
Proof with zsimpl;auto with zarith.
 induction p;destruct q;simpl;zsimpl;
  match goal with 
  | [|- context [(Pminus_mask ?p1 ?q1)]] => 
    assert (H1 := IHp q1);destruct (Pminus_mask p1 q1)
  | _ => idtac
  end;simpl ...
 inversion H1 ...   inversion H1 ...
 rewrite Psucc_Zplus in H1 ...
 clear IHp;induction p;simpl ...
  rewrite IHp;destruct (Pdouble_minus_one p) ...
 assert (H:= Zlt_0_pos q) ...   assert (H:= Zlt_0_pos q) ...
Qed.

Definition PminusN x y := 
  match Pminus_mask x y with
  | IsPos k => Npos k
  | _ => N0
  end.

Lemma PminusN_le : forall x y:positive, x <= y -> Z_of_N (PminusN y x) = y - x.
Proof.
 intros x y Hle;unfold PminusN.
 assert (H := Pminus_mask_spec y x);destruct (Pminus_mask y x).
 rewrite H;unfold Z_of_N;auto with zarith.
 rewrite H;unfold Z_of_N;auto with zarith.
 elimtype False;omega.
Qed.

Lemma Ppred_Zminus : forall p, 1< Zpos p ->  (p-1)%Z = Ppred p.
Proof. destruct p;simpl;trivial. intros;elimtype False;omega. Qed.


Open Local Scope positive_scope.

Delimit Scope P_scope with P.
Open Local Scope P_scope.

Definition is_lt (n m : positive) :=
  match (n ?= m) Eq with
  | Lt => true
  | _ => false
  end.
Infix "?<" := is_lt (at level 70, no associativity) : P_scope.

Lemma is_lt_spec : forall n m, if n ?< m then (n < m)%Z else (m <= n)%Z. 
Proof.
 intros n m; unfold is_lt, Zlt, Zle, Zcompare.
 rewrite (ZC4 m n);destruct ((n ?= m) Eq);trivial;try (intro;discriminate).
Qed.

Definition is_eq a b :=
  match (a ?= b) Eq with
  | Eq => true
  | _ => false
  end.
Infix "?=" := is_eq (at level 70, no associativity) : P_scope.
 
Lemma is_eq_refl : forall n, n ?= n = true.
Proof. intros n;unfold is_eq;rewrite Pcompare_refl;trivial. Qed.

Lemma is_eq_eq : forall n m, n ?= m = true -> n = m.
Proof.
 unfold is_eq;intros n m H; apply Pcompare_Eq_eq;
 destruct ((n ?= m)%positive Eq);trivial;try discriminate.
Qed.

Lemma is_eq_spec_pos : forall n m, if n ?= m then  n = m else  m <> n. 
Proof.
 intros n m; CaseEq (n ?= m);intro H.
 rewrite (is_eq_eq _ _ H);trivial.
 intro H1;rewrite H1 in H;rewrite is_eq_refl in H;discriminate H.
Qed.

Lemma is_eq_spec : forall n m, if n ?= m then Zpos n = m else Zpos m <> n. 
Proof.
 intros n m; CaseEq (n ?= m);intro H.
 rewrite (is_eq_eq _ _ H);trivial.
 intro H1;inversion H1.
 rewrite H2 in H;rewrite is_eq_refl in H;discriminate H.
Qed.

Definition is_Eq a b :=
  match a, b with
  | N0, N0 => true
  | Npos a', Npos b' => a' ?= b'
  | _, _ => false
  end.

Lemma is_Eq_spec : 
 forall n m, if is_Eq n m then Z_of_N n = m else Z_of_N m <> n. 
Proof.
 destruct n;destruct m;simpl;trivial;try (intro;discriminate).
 apply is_eq_spec.
Qed.

(* [times x y] return [x * y], a litle bit more efficiant *)
Fixpoint times (x y : positive) {struct y} : positive :=
  match x, y with
  | xH, _ => y
  | _, xH => x
  | xO x', xO y' => xO (xO (times x' y'))
  | xO x', xI y' => xO (x' + xO (times x' y'))
  | xI x', xO y' => xO (y' + xO (times x' y'))
  | xI x', xI y' => xI (x' + y' + xO (times x' y'))
  end.

Infix "*" := times : P_scope.

Lemma times_Zmult : forall p q, Zpos (p * q)%P = (p * q)%Z.
Proof.
 intros p q;generalize q p;clear p q.
 induction q;destruct p; unfold times; try fold (times p q);
   autorewrite with zmisc; try rewrite IHq; ring.
Qed.

Fixpoint square (x:positive) : positive :=
 match x with
 | xH => xH
 | xO x => xO (xO (square x))
 | xI x => xI (xO (square x + x))
 end.

Lemma square_Zmult : forall x, Zpos (square x) = (x * x) %Z.
Proof.
 induction x as [x IHx|x IHx |];unfold square;try (fold (square x));
   autorewrite with zmisc; try rewrite IHx; ring.
Qed.
