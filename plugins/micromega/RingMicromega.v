(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NArith.
Require Import Relation_Definitions.
Require Import Setoid.
(*****)
Require Import Env.
Require Import EnvRing.
(*****)
Require Import List.
Require Import Bool.
Require Import OrderedRing.
Require Import Refl.
Require Coq.micromega.Tauto.

Set Implicit Arguments.

Import OrderedRingSyntax.

Section Micromega.

(* Assume we have a strict(ly?) ordered ring *)

Variable R : Type.
Variables rO rI : R.
Variables rplus rtimes rminus: R -> R -> R.
Variable ropp : R -> R.
Variables req rle rlt : R -> R -> Prop.

Variable sor : SOR rO rI rplus rtimes rminus ropp req rle rlt.

Notation "0" := rO.
Notation "1" := rI.
Notation "x + y" := (rplus x y).
Notation "x * y " := (rtimes x y).
Notation "x - y " := (rminus x y).
Notation "- x" := (ropp x).
Notation "x == y" := (req x y).
Notation "x ~= y" := (~ req x y).
Notation "x <= y" := (rle x y).
Notation "x < y" := (rlt x y).

(* Assume we have a type of coefficients C and a morphism from C to R *)

Variable C : Type.
Variables cO cI : C.
Variables cplus ctimes cminus: C -> C -> C.
Variable copp : C -> C.
Variables ceqb cleb : C -> C -> bool.
Variable phi : C -> R.

(* Power coefficients *)
Variable E : Type. (* the type of exponents *)
Variable pow_phi : N -> E.
Variable rpow : R -> E -> R.

Notation "[ x ]" := (phi x).
Notation "x [=] y" := (ceqb x y).
Notation "x [<=] y" := (cleb x y).

(* Let's collect all hypotheses in addition to the ordered ring axioms into
one structure *)

Record SORaddon := mk_SOR_addon {
  SORrm : ring_morph 0 1 rplus rtimes rminus ropp req cO cI cplus ctimes cminus copp ceqb phi;
  SORpower : power_theory rI rtimes req pow_phi rpow;
  SORcneqb_morph : forall x y : C, x [=] y = false -> [x] ~= [y];
  SORcleb_morph : forall x y : C, x [<=] y = true -> [x] <= [y]
}.

Variable addon : SORaddon.

Add Relation R req
  reflexivity proved by sor.(SORsetoid).(@Equivalence_Reflexive _ _)
  symmetry proved by sor.(SORsetoid).(@Equivalence_Symmetric _ _)
  transitivity proved by sor.(SORsetoid).(@Equivalence_Transitive _ _)
as micomega_sor_setoid.

Add Morphism rplus with signature req ==> req ==> req as rplus_morph.
Proof.
exact sor.(SORplus_wd).
Qed.
Add Morphism rtimes with signature req ==> req ==> req as rtimes_morph.
Proof.
exact sor.(SORtimes_wd).
Qed.
Add Morphism ropp with signature req ==> req as ropp_morph.
Proof.
exact sor.(SORopp_wd).
Qed.
Add Morphism rle with signature req ==> req ==> iff as rle_morph.
Proof.
  exact sor.(SORle_wd).
Qed.
Add Morphism rlt with signature req ==> req ==> iff as rlt_morph.
Proof.
  exact sor.(SORlt_wd).
Qed.

Add Morphism rminus with signature req ==> req ==> req as rminus_morph.
Proof.
  exact (rminus_morph sor). (* We already proved that minus is a morphism in OrderedRing.v *)
Qed.

Definition cneqb (x y : C) := negb (ceqb x y).
Definition cltb (x y : C) := (cleb x y) && (cneqb x y).

Notation "x [~=] y" := (cneqb x y).
Notation "x [<] y" := (cltb x y).

Ltac le_less := rewrite (Rle_lt_eq sor); left; try assumption.
Ltac le_equal := rewrite (Rle_lt_eq sor); right; try reflexivity; try assumption.
Ltac le_elim H := rewrite (Rle_lt_eq sor) in H; destruct H as [H | H].

Lemma cleb_sound : forall x y : C, x [<=] y = true -> [x] <= [y].
Proof.
  exact addon.(SORcleb_morph).
Qed.

Lemma cneqb_sound : forall x y : C, x [~=] y = true -> [x] ~= [y].
Proof.
intros x y H1. apply addon.(SORcneqb_morph). unfold cneqb, negb in H1.
destruct (ceqb x y); now try discriminate.
Qed.


Lemma cltb_sound : forall x y : C, x [<] y = true -> [x] < [y].
Proof.
intros x y H. unfold cltb in H. apply andb_prop in H. destruct H as [H1 H2].
apply cleb_sound in H1. apply cneqb_sound in H2. apply <- (Rlt_le_neq sor). now split.
Qed.

(* Begin Micromega *)

Definition PolC := Pol C. (* polynomials in generalized Horner form, defined in Ring_polynom or EnvRing *)
Definition PolEnv := Env R. (* For interpreting PolC *)
Definition eval_pol : PolEnv -> PolC -> R :=
   Pphi rplus rtimes phi.

Inductive Op1 : Set := (* relations with 0 *)
| Equal (* == 0 *)
| NonEqual (* ~= 0 *)
| Strict (* > 0 *)
| NonStrict (* >= 0 *).

Definition NFormula := (PolC * Op1)%type. (* normalized formula *)

Definition eval_op1 (o : Op1) : R -> Prop :=
match o with
| Equal => fun x => x == 0
| NonEqual => fun x : R => x ~= 0
| Strict => fun x : R => 0 < x
| NonStrict => fun x : R => 0 <= x
end.

Definition eval_nformula (env : PolEnv) (f : NFormula) : Prop :=
let (p, op) := f in eval_op1 op (eval_pol env p).


(** Rule of "signs" for addition and multiplication.
   An arbitrary result is coded buy None. *)

Definition OpMult (o o' : Op1) : option Op1 :=
match o with
| Equal => Some Equal
| NonStrict =>
  match o' with
    | Equal => Some Equal
    | NonEqual  => None
    | Strict    => Some NonStrict
    | NonStrict => Some NonStrict
  end
| Strict => match o' with
              | NonEqual => None
              |  _       => Some o'
            end
| NonEqual => match o' with
                | Equal => Some Equal
                | NonEqual => Some NonEqual
                | _        => None
              end
end.

Definition OpAdd (o o': Op1) : option Op1 :=
  match o with
    | Equal => Some o'
    | NonStrict =>
      match o' with
        | Strict => Some Strict
        | NonEqual => None
        | _ => Some NonStrict
      end
    | Strict => match o' with
                  | NonEqual => None
                  |  _        => Some Strict
                end
    | NonEqual => match o' with
                    | Equal  => Some NonEqual
                    | _      => None
                  end
  end.


Lemma OpMult_sound :
  forall (o o' om: Op1) (x y : R),
    eval_op1 o x -> eval_op1 o' y -> OpMult o o' = Some om -> eval_op1 om (x * y).
Proof.
unfold eval_op1; destruct o; simpl; intros o' om x y H1 H2 H3.
(* x == 0 *)
inversion H3. rewrite H1. now rewrite (Rtimes_0_l sor).
(* x ~= 0 *)
destruct o' ; inversion H3.
 (* y == 0 *)
 rewrite H2. now rewrite (Rtimes_0_r sor).
 (* y ~= 0 *)
 apply (Rtimes_neq_0 sor) ; auto.
(* 0 < x *)
destruct o' ; inversion H3.
 (* y == 0 *)
 rewrite H2; now rewrite (Rtimes_0_r sor).
 (* 0 < y *)
 now apply (Rtimes_pos_pos sor).
 (* 0 <= y *)
  apply (Rtimes_nonneg_nonneg sor); [le_less | assumption].
(* 0 <= x *)
destruct o' ; inversion H3.
 (* y == 0 *)
 rewrite H2; now rewrite (Rtimes_0_r sor).
 (* 0 < y *)
 apply (Rtimes_nonneg_nonneg sor); [assumption | le_less ].
 (* 0 <= y *)
 now apply (Rtimes_nonneg_nonneg sor).
Qed.

Lemma OpAdd_sound :
  forall (o o' oa : Op1) (e e' : R),
    eval_op1 o e -> eval_op1 o' e' -> OpAdd o o' = Some oa -> eval_op1 oa (e + e').
Proof.
unfold eval_op1; destruct o; simpl; intros o' oa e e' H1 H2 Hoa.
(* e == 0 *)
inversion Hoa. rewrite <- H0.
destruct o' ; rewrite H1 ; now rewrite  (Rplus_0_l sor).
(* e ~= 0 *)
 destruct o'.
 (* e' == 0 *)
 inversion Hoa.
 rewrite H2. now rewrite (Rplus_0_r sor).
 (* e' ~= 0 *)
 discriminate.
 (* 0 < e' *)
 discriminate.
 (* 0 <= e' *)
 discriminate.
(* 0 < e *)
 destruct o'.
 (* e' == 0 *)
 inversion Hoa.
 rewrite H2.  now rewrite (Rplus_0_r sor).
 (* e' ~= 0 *)
 discriminate.
 (* 0 < e' *)
 inversion Hoa.
 now apply (Rplus_pos_pos sor).
 (* 0 <= e' *)
 inversion Hoa.
 now apply (Rplus_pos_nonneg sor).
(* 0 <= e *)
 destruct o'.
 (* e' == 0 *)
 inversion Hoa.
 now rewrite H2, (Rplus_0_r sor).
 (* e' ~= 0 *)
 discriminate.
 (* 0 < e' *)
 inversion Hoa.
 now apply (Rplus_nonneg_pos sor).
 (* 0 <= e' *)
 inversion Hoa.
 now apply (Rplus_nonneg_nonneg sor).
Qed.

Inductive Psatz : Type :=
| PsatzIn : nat -> Psatz
| PsatzSquare : PolC -> Psatz
| PsatzMulC : PolC -> Psatz -> Psatz
| PsatzMulE : Psatz -> Psatz -> Psatz
| PsatzAdd  : Psatz -> Psatz -> Psatz
| PsatzC    : C -> Psatz
| PsatzZ    : Psatz.

(** Given a list [l] of NFormula and an extended polynomial expression
   [e], if [eval_Psatz l e] succeeds (= Some f) then [f] is a
   logic consequence of the conjunction of the formulae in l.
   Moreover, the polynomial expression is obtained by replacing the (PsatzIn n)
   by the nth polynomial expression in [l] and the sign is computed by the "rule of sign" *)

(* Might be defined elsewhere *)
Definition map_option (A B:Type) (f : A -> option B) (o : option A) : option B :=
  match o with
    | None => None
    | Some x => f x
  end.

Arguments map_option [A B] f o.

Definition map_option2 (A B C : Type) (f : A -> B -> option C)
  (o: option A) (o': option B) : option C :=
  match o , o' with
    | None , _ => None
    | _ , None => None
    | Some x , Some x' => f x x'
  end.

Arguments map_option2 [A B C] f o o'.

Definition Rops_wd := mk_reqe (*rplus rtimes ropp req*)
                       sor.(SORplus_wd)
                       sor.(SORtimes_wd)
                       sor.(SORopp_wd).

Definition pexpr_times_nformula (e: PolC) (f : NFormula) : option NFormula :=
  let (ef,o) := f in
    match o with
      | Equal => Some (Pmul cO cI cplus ctimes ceqb e ef , Equal)
      |   _   => None
    end.

Definition nformula_times_nformula (f1 f2 : NFormula) : option NFormula :=
  let (e1,o1) := f1 in
    let (e2,o2) := f2 in
      map_option  (fun x => (Some (Pmul cO cI cplus ctimes ceqb e1 e2,x)))    (OpMult o1 o2).

 Definition nformula_plus_nformula (f1 f2 : NFormula) : option NFormula :=
  let (e1,o1) := f1 in
    let (e2,o2) := f2 in
      map_option  (fun x => (Some (Padd cO cplus ceqb e1 e2,x)))    (OpAdd o1 o2).


Fixpoint eval_Psatz (l : list NFormula) (e : Psatz) {struct e} : option NFormula :=
  match e with
    | PsatzIn n => Some (nth n l (Pc cO, Equal))
    | PsatzSquare e => Some (Psquare cO cI cplus ctimes ceqb e  , NonStrict)
    | PsatzMulC re e => map_option (pexpr_times_nformula re) (eval_Psatz l e)
    | PsatzMulE f1 f2 => map_option2 nformula_times_nformula  (eval_Psatz l f1) (eval_Psatz l f2)
    | PsatzAdd f1 f2  => map_option2 nformula_plus_nformula  (eval_Psatz l f1) (eval_Psatz l f2)
    | PsatzC  c  => if cltb cO c then Some (Pc c, Strict) else None
(* This could be 0, or <> 0 -- but these cases are useless *)
    | PsatzZ     => Some (Pc cO, Equal) (* Just to make life easier *)
  end.


Lemma pexpr_times_nformula_correct : forall (env: PolEnv) (e: PolC) (f f' : NFormula),
  eval_nformula env f -> pexpr_times_nformula e f = Some f' ->
   eval_nformula env f'.
Proof.
  unfold pexpr_times_nformula.
  destruct f.
  intros. destruct o ; inversion H0 ; try discriminate.
  simpl in *.    unfold eval_pol in *.
  rewrite (Pmul_ok sor.(SORsetoid) Rops_wd
    (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt))  addon.(SORrm)).
  rewrite H. apply (Rtimes_0_r sor).
Qed.

Lemma nformula_times_nformula_correct : forall (env:PolEnv)
  (f1 f2 f : NFormula),
  eval_nformula env f1 -> eval_nformula env f2 ->
  nformula_times_nformula f1 f2 = Some f  ->
   eval_nformula env f.
Proof.
  unfold nformula_times_nformula.
  destruct f1 ; destruct f2.
  case_eq (OpMult o o0) ; simpl ; try discriminate.
  intros. inversion H2 ; simpl.
  unfold eval_pol.
  destruct o1; simpl;
  rewrite (Pmul_ok sor.(SORsetoid) Rops_wd
    (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt))  addon.(SORrm));
  apply OpMult_sound with (3:= H);assumption.
Qed.

Lemma nformula_plus_nformula_correct : forall (env:PolEnv)
  (f1 f2 f : NFormula),
  eval_nformula env f1 -> eval_nformula env f2 ->
  nformula_plus_nformula f1 f2 = Some f  ->
   eval_nformula env f.
Proof.
  unfold nformula_plus_nformula.
  destruct f1 ; destruct f2.
  case_eq (OpAdd o o0) ; simpl ; try discriminate.
  intros. inversion H2 ; simpl.
  unfold eval_pol.
  destruct o1; simpl;
  rewrite (Padd_ok sor.(SORsetoid) Rops_wd
    (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt))  addon.(SORrm));
  apply OpAdd_sound with (3:= H);assumption.
Qed.

Lemma eval_Psatz_Sound :
  forall (l : list NFormula) (env : PolEnv),
    (forall (f : NFormula), In f l -> eval_nformula env f) ->
      forall (e : Psatz) (f : NFormula), eval_Psatz l e = Some f ->
        eval_nformula env f.
Proof.
  induction e.
  (* PsatzIn *)
  simpl ; intros.
  destruct (nth_in_or_default n l (Pc cO, Equal)) as [Hin|Heq].
  (* index is in bounds *)
  apply H. congruence.
  (* index is out-of-bounds *)
  inversion H0.
  rewrite Heq. simpl.
  now apply  addon.(SORrm).(morph0).
  (* PsatzSquare *)
  simpl. intros. inversion H0.
  simpl. unfold eval_pol.
  rewrite (Psquare_ok sor.(SORsetoid) Rops_wd
    (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt))  addon.(SORrm));
  now apply (Rtimes_square_nonneg sor).
  (* PsatzMulC *)
  simpl.
  intro.
  case_eq  (eval_Psatz l e) ; simpl ; intros.
  apply IHe in H0.
  apply pexpr_times_nformula_correct with (1:=H0) (2:= H1).
  discriminate.
  (* PsatzMulC *)
  simpl ; intro.
  case_eq (eval_Psatz l e1) ; simpl ; try discriminate.
  case_eq (eval_Psatz l e2) ; simpl ; try discriminate.
  intros.
  apply IHe1 in H1. apply IHe2 in H0.
  apply (nformula_times_nformula_correct env n0 n) ; assumption.
  (* PsatzAdd *)
  simpl ; intro.
  case_eq (eval_Psatz l e1) ; simpl ; try discriminate.
  case_eq (eval_Psatz l e2) ; simpl ; try discriminate.
  intros.
  apply IHe1 in H1. apply IHe2 in H0.
  apply (nformula_plus_nformula_correct env n0 n) ; assumption.
  (* PsatzC *)
  simpl.
  intro. case_eq (cO [<] c).
  intros.  inversion H1. simpl.
  rewrite <- addon.(SORrm).(morph0). now apply cltb_sound.
  discriminate.
  (* PsatzZ *)
  simpl. intros. inversion H0.
  simpl.   apply  addon.(SORrm).(morph0).
Qed.

Fixpoint ge_bool (n m  : nat) : bool :=
 match n with
   | O   => match m with
            |  O => true
            | S _ => false
          end
   | S n  => match m with
               | O => true
               | S m => ge_bool n m
             end
   end.

Lemma ge_bool_cases : forall n m,
 (if ge_bool n m then n >= m else n < m)%nat.
Proof.
  induction n; destruct m ; simpl; auto with arith.
  specialize (IHn m). destruct (ge_bool); auto with arith.
Qed.


Fixpoint xhyps_of_psatz (base:nat) (acc : list nat) (prf : Psatz)  : list nat :=
  match prf with
    | PsatzC _ | PsatzZ | PsatzSquare _ => acc
    | PsatzMulC _ prf => xhyps_of_psatz base acc prf
    | PsatzAdd e1 e2 | PsatzMulE e1 e2 => xhyps_of_psatz base (xhyps_of_psatz base acc e2) e1
    | PsatzIn n => if ge_bool n base then (n::acc) else acc
  end.

Fixpoint nhyps_of_psatz (prf : Psatz) : list nat :=
  match prf with
    | PsatzC _ | PsatzZ | PsatzSquare _ => nil
    | PsatzMulC _ prf => nhyps_of_psatz prf
    | PsatzAdd e1 e2 | PsatzMulE e1 e2 => nhyps_of_psatz e1 ++ nhyps_of_psatz e2
    | PsatzIn n => n :: nil
  end.


Fixpoint extract_hyps (l: list NFormula) (ln : list nat) : list NFormula  :=
  match ln with
    | nil => nil
    | n::ln => nth n l (Pc cO, Equal) :: extract_hyps l ln
  end.
      
Lemma extract_hyps_app : forall l ln1 ln2,
  extract_hyps l (ln1 ++ ln2) = (extract_hyps l ln1) ++ (extract_hyps l ln2).
Proof.
  induction ln1.
  reflexivity.
  simpl.
  intros.
  rewrite IHln1. reflexivity.
Qed.
  
Ltac inv H := inversion H ; try subst ; clear H.

Lemma nhyps_of_psatz_correct :  forall (env : PolEnv) (e:Psatz)  (l : list NFormula)  (f: NFormula),
  eval_Psatz l e = Some f -> 
  ((forall f', In f' (extract_hyps l (nhyps_of_psatz e)) -> eval_nformula env f') ->  eval_nformula env f).
Proof.
  induction e ; intros.
  (*PsatzIn*)
  simpl in *. 
  apply H0. intuition congruence.
  (* PsatzSquare *)
  simpl in *.
  inv H.
  simpl.
  unfold eval_pol.
  rewrite (Psquare_ok sor.(SORsetoid) Rops_wd
    (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt))  addon.(SORrm));
  now apply (Rtimes_square_nonneg sor).
  (* PsatzMulC *)
  simpl in *.
  case_eq (eval_Psatz l e).
  intros. rewrite H1 in H. simpl in H.
  apply pexpr_times_nformula_correct with (2:= H).
  apply IHe with (1:= H1); auto.
  intros. rewrite H1 in H. simpl in H ; discriminate.
  (* PsatzMulE *)
  simpl in *.
  revert H.
  case_eq (eval_Psatz l e1).
  case_eq (eval_Psatz l e2) ; simpl ; intros.
  apply nformula_times_nformula_correct with (3:= H2).
  apply IHe1 with (1:= H1) ; auto.
  intros. apply H0. rewrite extract_hyps_app.
  apply in_or_app. tauto.
  apply IHe2 with (1:= H) ; auto.
  intros. apply H0. rewrite extract_hyps_app.
  apply in_or_app. tauto.
  discriminate. simpl. discriminate.
  (* PsatzAdd *)
  simpl in *.
  revert H.
  case_eq (eval_Psatz l e1).
  case_eq (eval_Psatz l e2) ; simpl ; intros.
  apply nformula_plus_nformula_correct with (3:= H2).
  apply IHe1 with (1:= H1) ; auto.
  intros. apply H0. rewrite extract_hyps_app.
  apply in_or_app. tauto.
  apply IHe2 with (1:= H) ; auto.
  intros. apply H0. rewrite extract_hyps_app.
  apply in_or_app. tauto.
  discriminate. simpl. discriminate.
  (* PsatzC *)
  simpl in H.
  case_eq (cO [<] c).
  intros.  rewrite H1 in H. inv H.
  unfold eval_nformula. simpl.
  rewrite <- addon.(SORrm).(morph0). now apply cltb_sound.
  intros. rewrite H1 in H. discriminate.
  (* PsatzZ *)
  simpl in *. inv H. 
  unfold eval_nformula. simpl.
  apply  addon.(SORrm).(morph0).
Qed.
  





(* roughly speaking, normalise_pexpr_correct is a proof of
  forall env p, eval_pexpr env p == eval_pol env (normalise_pexpr p) *)

(*****)
Definition paddC := PaddC cplus.
Definition psubC := PsubC cminus.

Definition PsubC_ok : forall c P env, eval_pol env (psubC  P c) == eval_pol env P - [c] :=
  let Rops_wd := mk_reqe (*rplus rtimes ropp req*)
                       sor.(SORplus_wd)
                       sor.(SORtimes_wd)
                       sor.(SORopp_wd) in
                       PsubC_ok sor.(SORsetoid) Rops_wd (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt))
                addon.(SORrm).

Definition PaddC_ok : forall c P env, eval_pol env (paddC  P c) == eval_pol env P + [c] :=
  let Rops_wd := mk_reqe (*rplus rtimes ropp req*)
                       sor.(SORplus_wd)
                       sor.(SORtimes_wd)
                       sor.(SORopp_wd) in
                       PaddC_ok sor.(SORsetoid) Rops_wd (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt))
                addon.(SORrm).


(* Check that a formula f is inconsistent by normalizing and comparing the
resulting constant with 0 *)

Definition check_inconsistent (f : NFormula) : bool :=
let (e, op) := f in
  match  e with
  | Pc c =>
    match op with
    | Equal => cneqb c cO
    | NonStrict => c [<] cO
    | Strict => c [<=] cO
    | NonEqual => c [=] cO
    end
  | _ => false (* not a constant *)
  end.

Lemma check_inconsistent_sound :
  forall (p : PolC) (op : Op1),
    check_inconsistent (p, op) = true -> forall env, ~ eval_op1 op (eval_pol env p).
Proof.
intros p op H1 env. unfold check_inconsistent in H1.
destruct op; simpl ;
(*****)
destruct p ; simpl; try discriminate H1;
try rewrite <- addon.(SORrm).(morph0); trivial.
now apply cneqb_sound.
apply addon.(SORrm).(morph_eq) in H1. congruence.
apply cleb_sound in H1. now apply -> (Rle_ngt sor).
apply cltb_sound in H1. now apply -> (Rlt_nge sor).
Qed.


Definition check_normalised_formulas : list NFormula -> Psatz -> bool :=
  fun l cm =>
    match eval_Psatz l cm with
      | None => false
      | Some f => check_inconsistent f
    end.

Lemma checker_nf_sound :
  forall (l : list NFormula) (cm : Psatz),
    check_normalised_formulas l cm = true ->
      forall env : PolEnv, make_impl (eval_nformula env) l False.
Proof.
intros l cm H env.
unfold check_normalised_formulas in H.
revert H.
case_eq (eval_Psatz l cm) ; [|discriminate].
intros nf. intros.
rewrite <- make_conj_impl. intro.
assert (H1' := make_conj_in _ _ H1).
assert (Hnf :=  @eval_Psatz_Sound  _ _  H1' _ _ H).
destruct nf.
apply (@check_inconsistent_sound _ _ H0 env Hnf).
Qed.

(** Normalisation of formulae **)

Inductive Op2 : Set := (* binary relations *)
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt.

Definition eval_op2 (o : Op2) : R -> R -> Prop :=
match o with
| OpEq => req
| OpNEq => fun x y : R => x ~= y
| OpLe => rle
| OpGe => fun x y : R => y <= x
| OpLt => fun x y : R => x < y
| OpGt => fun x y : R => y < x
end.

Definition  eval_pexpr : PolEnv -> PExpr C -> R :=
 PEeval rplus rtimes rminus ropp phi pow_phi rpow.

Record Formula (T:Type) : Type := {
  Flhs : PExpr T;
  Fop : Op2;
  Frhs : PExpr T
}.

Definition eval_formula (env : PolEnv) (f : Formula C) : Prop :=
  let (lhs, op, rhs) := f in
    (eval_op2 op) (eval_pexpr env lhs) (eval_pexpr env rhs).


(* We normalize Formulas by moving terms to one side *)

Definition norm := norm_aux cO cI cplus ctimes cminus copp ceqb.

Definition psub := Psub cO  cplus cminus copp ceqb.

Definition padd  := Padd cO  cplus ceqb.

Definition normalise (f : Formula C) : NFormula :=
let (lhs, op, rhs) := f in
  let lhs := norm lhs in
    let rhs := norm rhs in
  match op with
  | OpEq =>  (psub  lhs rhs, Equal)
  | OpNEq => (psub lhs rhs, NonEqual)
  | OpLe =>  (psub rhs lhs, NonStrict)
  | OpGe =>  (psub lhs rhs, NonStrict)
  | OpGt => (psub  lhs rhs, Strict)
  | OpLt => (psub  rhs lhs, Strict)
  end.

Definition negate (f : Formula C) : NFormula :=
let (lhs, op, rhs) := f in
  let lhs := norm lhs in
    let rhs := norm rhs in
      match op with
        | OpEq => (psub rhs lhs, NonEqual)
        | OpNEq => (psub rhs lhs, Equal)
        | OpLe => (psub lhs rhs, Strict) (* e <= e' == ~ e > e' *)
        | OpGe => (psub rhs lhs, Strict)
        | OpGt => (psub rhs lhs, NonStrict)
        | OpLt => (psub lhs rhs, NonStrict)
      end.


Lemma eval_pol_sub : forall env lhs rhs, eval_pol env (psub  lhs rhs) == eval_pol env lhs - eval_pol env rhs.
Proof.
  intros.
  apply (Psub_ok  sor.(SORsetoid) Rops_wd
    (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt)) addon.(SORrm)).
Qed.

Lemma eval_pol_add : forall env lhs rhs, eval_pol env (padd  lhs rhs) == eval_pol env lhs + eval_pol env rhs.
Proof.
  intros.
  apply (Padd_ok  sor.(SORsetoid) Rops_wd
    (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt)) addon.(SORrm)).
Qed.

Lemma eval_pol_norm : forall env lhs, eval_pexpr env lhs == eval_pol env  (norm lhs).
Proof.
  intros.
  apply  (norm_aux_spec sor.(SORsetoid) Rops_wd   (Rth_ARth (SORsetoid sor) Rops_wd sor.(SORrt)) addon.(SORrm) addon.(SORpower) ).
Qed.


Theorem normalise_sound :
  forall (env : PolEnv) (f : Formula C),
    eval_formula env f -> eval_nformula env (normalise f).
Proof.
intros env f H; destruct f as [lhs op rhs]; simpl in *.
destruct op; simpl in *; rewrite eval_pol_sub ; rewrite <- eval_pol_norm ; rewrite <- eval_pol_norm.
now apply <- (Rminus_eq_0 sor).
intros H1. apply -> (Rminus_eq_0 sor) in H1. now apply H.
now apply -> (Rle_le_minus sor).
now apply -> (Rle_le_minus sor).
now apply -> (Rlt_lt_minus sor).
now apply -> (Rlt_lt_minus sor).
Qed.

Theorem negate_correct :
  forall (env : PolEnv) (f : Formula C),
    eval_formula env f <-> ~ (eval_nformula env (negate f)).
Proof.
intros env f; destruct f as [lhs op rhs]; simpl.
destruct op; simpl in *; rewrite eval_pol_sub ; rewrite <- eval_pol_norm ; rewrite <- eval_pol_norm.
symmetry. rewrite (Rminus_eq_0 sor).
split; intro H; [symmetry; now apply -> (Req_dne sor) | symmetry in H; now apply <- (Req_dne sor)].
rewrite (Rminus_eq_0 sor). split; intro; now apply (Rneq_symm sor).
rewrite <- (Rlt_lt_minus sor). now rewrite <- (Rle_ngt sor).
rewrite <- (Rlt_lt_minus sor). now rewrite <- (Rle_ngt sor).
rewrite <- (Rle_le_minus sor). now rewrite <- (Rlt_nge sor).
rewrite <- (Rle_le_minus sor). now rewrite <- (Rlt_nge sor).
Qed.

(** Another normalisation - this is used for cnf conversion **)

Definition xnormalise (t:Formula C) : list (NFormula)  :=
  let (lhs,o,rhs) := t in
  let lhs := norm lhs in
    let rhs := norm rhs in
    match o with
      | OpEq =>
        (psub lhs  rhs, Strict)::(psub rhs lhs , Strict)::nil
      | OpNEq => (psub lhs rhs,Equal) :: nil
      | OpGt   => (psub rhs lhs,NonStrict) :: nil
      | OpLt => (psub lhs rhs,NonStrict) :: nil
      | OpGe => (psub rhs lhs , Strict) :: nil
      | OpLe => (psub lhs rhs ,Strict) :: nil
    end.

Import Coq.micromega.Tauto.

Definition cnf_normalise (t:Formula C) : cnf (NFormula) :=
  List.map  (fun x => x::nil) (xnormalise t).


Add Ring SORRing : sor.(SORrt).

Lemma cnf_normalise_correct : forall env t, eval_cnf eval_nformula env (cnf_normalise t) -> eval_formula env t.
Proof.
  unfold cnf_normalise, xnormalise ; simpl ; intros env t.
  unfold eval_cnf, eval_clause.
  destruct t as [lhs o rhs]; case_eq o ; simpl;
    repeat rewrite eval_pol_sub ; repeat rewrite <- eval_pol_norm in * ;
    generalize (eval_pexpr  env lhs);
      generalize (eval_pexpr  env rhs) ; intros z1 z2 ; intros.
  (**)
  apply sor.(SORle_antisymm).
  rewrite  (Rle_ngt sor). rewrite (Rlt_lt_minus sor). tauto.
  rewrite  (Rle_ngt sor). rewrite (Rlt_lt_minus sor). tauto.
  now rewrite <- (Rminus_eq_0 sor).
  rewrite (Rle_ngt sor).  rewrite (Rlt_lt_minus sor). auto.
  rewrite (Rle_ngt sor).  rewrite (Rlt_lt_minus sor). auto.
  rewrite (Rlt_nge sor).  rewrite (Rle_le_minus sor). auto.
  rewrite (Rlt_nge sor).  rewrite (Rle_le_minus sor). auto.
Qed.

Definition xnegate (t:Formula C) : list (NFormula)  :=
  let (lhs,o,rhs) := t in
    let lhs := norm lhs in
      let rhs := norm rhs in
    match o with
      | OpEq  => (psub lhs rhs,Equal) :: nil
      | OpNEq => (psub lhs  rhs ,Strict)::(psub rhs lhs,Strict)::nil
      | OpGt  => (psub lhs  rhs,Strict) :: nil
      | OpLt  => (psub rhs lhs,Strict) :: nil
      | OpGe  => (psub lhs rhs,NonStrict) :: nil
      | OpLe  => (psub rhs lhs,NonStrict) :: nil
    end.

Definition cnf_negate (t:Formula C) : cnf (NFormula) :=
  List.map  (fun x => x::nil) (xnegate t).

Lemma cnf_negate_correct : forall env t, eval_cnf eval_nformula env (cnf_negate t) -> ~ eval_formula env t.
Proof.
  unfold cnf_negate, xnegate ; simpl ; intros env t.
  unfold eval_cnf, eval_clause.
  destruct t as [lhs o rhs]; case_eq o ; simpl;
    repeat rewrite eval_pol_sub ; repeat rewrite <- eval_pol_norm in * ;
    generalize (eval_pexpr  env lhs);
      generalize (eval_pexpr  env rhs) ; intros z1 z2 ; intros ; intuition.
  (**)
  apply H0.
  rewrite H1 ; ring.
  (**)
  apply H1.
  apply sor.(SORle_antisymm).
  rewrite  (Rle_ngt sor). rewrite (Rlt_lt_minus sor). tauto.
  rewrite  (Rle_ngt sor). rewrite (Rlt_lt_minus sor). tauto.
  (**)
  apply H0. now rewrite  (Rle_le_minus sor) in H1.
  apply H0. now rewrite (Rle_le_minus sor) in H1.
  apply H0. now rewrite (Rlt_lt_minus sor) in H1.
  apply H0. now rewrite (Rlt_lt_minus sor) in H1.
Qed.

Lemma eval_nformula_dec : forall env d, (eval_nformula env d) \/ ~ (eval_nformula env d).
Proof.
  intros.
  destruct d ; simpl.
  generalize (eval_pol env p); intros.
  destruct o ; simpl.
  apply (Req_em sor r 0).
  destruct (Req_em sor r 0) ; tauto.
  rewrite <- (Rle_ngt sor r 0). generalize (Rle_gt_cases sor r 0). tauto.
  rewrite <- (Rlt_nge sor r 0). generalize (Rle_gt_cases sor 0 r). tauto.
Qed.

(** Reverse transformation *)

Fixpoint xdenorm (jmp : positive) (p: Pol C) : PExpr C :=
  match p with
    | Pc c => PEc c
    | Pinj j p => xdenorm  (Pos.add j jmp ) p
    | PX p j q   => PEadd
      (PEmul (xdenorm jmp p) (PEpow (PEX _  jmp) (Npos j)))
      (xdenorm (Pos.succ jmp) q)
  end.

Lemma xdenorm_correct : forall p i env,
  eval_pol (jump i env) p == eval_pexpr env (xdenorm (Pos.succ i) p).
Proof.
  unfold eval_pol.
  induction p.
  simpl. reflexivity.
  (* Pinj *)
  simpl.
  intros.
  rewrite Pos.add_succ_r.
  rewrite <- IHp.
  symmetry.
  rewrite Pos.add_comm.
  rewrite Pjump_add. reflexivity.
  (* PX *)
  simpl.
  intros.
  rewrite <- IHp1, <- IHp2.
  unfold Env.tail , Env.hd.
  rewrite <- Pjump_add.
  rewrite Pos.add_1_r.
  unfold Env.nth.
  unfold jump at 2.
  rewrite <- Pos.add_1_l.
  rewrite addon.(SORpower).(rpow_pow_N).
  unfold pow_N. ring.
Qed.

Definition denorm := xdenorm xH.

Lemma denorm_correct : forall p env, eval_pol env p == eval_pexpr env (denorm p).
Proof.
  unfold denorm.
  induction p.
  reflexivity.
  simpl.
  rewrite Pos.add_1_r.
  apply xdenorm_correct.
  simpl.
  intros.
  rewrite IHp1.
  unfold Env.tail.
  rewrite xdenorm_correct.
  change (Pos.succ xH) with 2%positive.
  rewrite addon.(SORpower).(rpow_pow_N).
  simpl. reflexivity.
Qed.


(** Sometimes it is convenient to make a distinction between "syntactic" coefficients and "real"
coefficients that are used to actually compute *)



Variable S : Type.

Variable C_of_S : S -> C.

Variable phiS : S -> R.

Variable phi_C_of_S :   forall c,  phiS c =  phi (C_of_S c).

Fixpoint map_PExpr (e : PExpr S) : PExpr C :=
  match e with
    | PEc c => PEc (C_of_S c)
    | PEX _ p => PEX _ p
    | PEadd e1 e2 => PEadd (map_PExpr e1) (map_PExpr e2)
    | PEsub e1 e2 => PEsub (map_PExpr e1) (map_PExpr e2)
    | PEmul e1 e2 => PEmul (map_PExpr e1) (map_PExpr e2)
    | PEopp e     => PEopp (map_PExpr e)
    | PEpow e n   => PEpow (map_PExpr e) n
  end.

Definition map_Formula (f : Formula S)  : Formula C :=
  let (l,o,r) := f in
    Build_Formula (map_PExpr l) o (map_PExpr r).


Definition eval_sexpr : PolEnv -> PExpr S -> R :=
  PEeval rplus rtimes rminus ropp phiS pow_phi rpow.

Definition eval_sformula (env : PolEnv) (f : Formula S) : Prop :=
  let (lhs, op, rhs) := f in
    (eval_op2 op) (eval_sexpr env lhs) (eval_sexpr env rhs).

Lemma eval_pexprSC : forall env s, eval_sexpr env s = eval_pexpr env (map_PExpr s).
Proof.
  unfold eval_pexpr, eval_sexpr.
  induction s ; simpl ; try (rewrite IHs1 ; rewrite IHs2) ; try reflexivity.
  apply phi_C_of_S.
  rewrite IHs. reflexivity.
  rewrite IHs. reflexivity.
Qed.

(** equality migth be (too) strong *)
Lemma eval_formulaSC : forall env f, eval_sformula env f = eval_formula env (map_Formula f).
Proof.
  destruct f.
  simpl.
  repeat rewrite eval_pexprSC.
  reflexivity.
Qed.




(** Some syntactic simplifications of expressions  *)


Definition simpl_cone (e:Psatz) : Psatz :=
  match e with
    | PsatzSquare t =>
                    match t with
                      | Pc c   => if ceqb cO c then PsatzZ else PsatzC (ctimes c c)
                      | _ => PsatzSquare t
                    end
    | PsatzMulE t1 t2 =>
      match t1 , t2 with
        | PsatzZ      , x        => PsatzZ
        |    x     , PsatzZ      => PsatzZ
        | PsatzC c ,  PsatzC c' => PsatzC (ctimes c c')
        | PsatzC p1 , PsatzMulE (PsatzC p2)  x => PsatzMulE (PsatzC (ctimes p1 p2)) x
        | PsatzC p1 , PsatzMulE x (PsatzC p2)  => PsatzMulE (PsatzC (ctimes p1 p2)) x
        | PsatzMulE (PsatzC p2)  x  , PsatzC p1   => PsatzMulE (PsatzC (ctimes p1 p2)) x
        | PsatzMulE x (PsatzC p2)   , PsatzC p1   => PsatzMulE (PsatzC (ctimes p1 p2)) x
        | PsatzC x   , PsatzAdd y z   => PsatzAdd (PsatzMulE (PsatzC x) y) (PsatzMulE (PsatzC x) z)
        | PsatzC c ,  _        => if ceqb cI c then t2 else PsatzMulE t1 t2
        | _ ,  PsatzC c        => if ceqb cI c then t1 else PsatzMulE t1 t2
        |     _     , _   => e
      end
    | PsatzAdd t1 t2 =>
      match t1 ,  t2 with
        | PsatzZ     , x => x
        |   x     , PsatzZ => x
        |   x     , y   => PsatzAdd x y
      end
    |   _     => e
  end.




End Micromega.

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
