Axiom magic : False.

(* Submitted by Dachuan Yu (BZ#220) *)
Fixpoint T (n : nat) : Type :=
  match n with
  | O => nat -> Prop
  | S n' => T n'
  end.
Inductive R : forall n : nat, T n -> nat -> Prop :=
  | RO : forall (Psi : T 0) (l : nat), Psi l -> R 0 Psi l
  | RS :
      forall (n : nat) (Psi : T (S n)) (l : nat), R n Psi l -> R (S n) Psi l.
Definition Psi00 (n : nat) : Prop := False.
Definition Psi0 : T 0 := Psi00.
Lemma Inversion_RO : forall l : nat, R 0 Psi0 l -> Psi00 l.
inversion 1.
Abort.

(* Submitted by Pierre Casteran (BZ#540) *)

Set Implicit Arguments.
Unset Strict Implicit.
Parameter rule : Set -> Type.

Inductive extension (I : Set) : Type :=
  | NL : extension I
  | add_rule : rule I -> extension I -> extension I.


Inductive in_extension (I : Set) (r : rule I) : extension I -> Type :=
  | in_first : forall e, in_extension r (add_rule r e)
  | in_rest : forall e r', in_extension r e -> in_extension r (add_rule r' e).

Arguments NL [I].

Inductive super_extension (I : Set) (e : extension I) :
extension I -> Type :=
  | super_NL : super_extension e NL
  | super_add :
      forall r (e' : extension I),
      in_extension r e ->
      super_extension e e' -> super_extension e (add_rule r e').



Lemma super_def :
 forall (I : Set) (e1 e2 : extension I),
 super_extension e2 e1 -> forall ru, in_extension ru e1 -> in_extension ru e2.
Proof.
 simple induction 1.
 inversion 1; auto.
 elim magic.
Qed.

(* Example from Norbert Schirmer on Coq-Club, Sep 2000 *)

Set Strict Implicit.
Unset Implicit Arguments.
Definition Q (n m : nat) (prf : n <= m) := True.
Goal forall (n m : nat) (H : S n <= m), Q (S n) m H = True.
intros.
dependent inversion_clear H.
elim magic.
elim magic.
Qed.

(* Submitted by Boris Yakobowski (BZ#529) *)
(* Check that Inversion does not fail due to unnormalized evars *)

Set Implicit Arguments.
Unset Strict Implicit.
Require Import Bvector.

Inductive I : nat -> Set :=
  | C1 : I 1
  | C2 : forall k i : nat, Vector.t (I i) k -> I i.

Inductive SI : forall k : nat, I k -> Vector.t nat k -> nat -> Prop :=
    SC2 :
      forall (k i vf : nat) (v : Vector.t (I i) k) (xi : Vector.t nat i),
      SI (C2 v) xi vf.

Theorem SUnique :
 forall (k : nat) (f : I k) (c : Vector.t nat k) v v',
 SI f c v -> SI f c v' -> v = v'.
Proof.
induction 1.
intros H; inversion H.
Admitted.

(* Used to failed at some time *)

Set Strict Implicit.
Unset Implicit Arguments.
Parameter bar : forall p q : nat, p = q -> Prop.
Inductive foo : nat -> nat -> Prop :=
    C : forall (a b : nat) (Heq : a = b), bar a b Heq -> foo a b.
Lemma depinv : forall a b, foo a b -> True.
intros a b H.
inversion H.
Abort.

(* Check non-regression of BZ#1968 *)

Inductive foo2 : option nat -> Prop := Foo : forall t, foo2 (Some t).
Goal forall o, foo2 o -> 0 = 1.
intros.
eapply trans_eq.
inversion H.
Abort.

(* Check that the part of "injection" that is called by "inversion"
   does the same number of intros as the number of equations
   introduced, even in presence of dependent equalities that
   "injection" renounces to split *)

Fixpoint prodn (n : nat) :=
  match n with
  | O => unit
  | (S m) => prod (prodn m) nat
  end.

Inductive U : forall n : nat, prodn n -> bool -> Prop :=
| U_intro : U 0 tt true.

Lemma foo3 : forall n (t : prodn n), U n t true -> False.
Proof.
(* used to fail because dEqThen thought there were 2 new equations but
   inject_at_positions actually introduced only one; leading then to
   an inconsistent state that disturbed "inversion" *)
intros. inversion H.
Abort.

(* BZ#2314 (simplified): check that errors do not show as anomalies *)

Goal True -> True.
intro.
Fail inversion H using False.
Fail inversion foo using True_ind.
Abort.

(* Was failing at some time between 7 and 10 September 2014 *)
(* even though, it is not clear that the resulting context is interesting *)

Parameter P:nat*nat->Prop.
Inductive IND : nat * nat -> { x : nat * nat | P x } * nat -> Prop :=
CONSTR a b (H:P (a,b)) c : IND (a,b) (exist _ (a,b) H, c).

Goal forall x y z t u (H':P (z,t)), IND (x,y) (exist _ (z,t) H', u) -> x = z.
intros * Hyp.
inversion Hyp.
  (* By the way, why is "H" removed even in non-clear mode ? *)
reflexivity.
Qed.

Goal forall x y z t u (H':P (z,t)), IND (x,y) (exist _ (z,t) H', u) -> x = z.
intros * Hyp.
inversion Hyp as (a,b,H,c,(H1_1,H1_2),(H2_1,H2_2,H2_3)).
reflexivity.
Qed.

(* Up to September 2014, Mapp below was called MApp0 because of a bug
   in intro_replacing (short version of BZ#2164.v)
   (example taken from CoLoR) *)

Parameter Term : Type.
Parameter isApp : Term -> Prop.
Parameter appBodyL : forall M, isApp M -> Prop.
Parameter lower : forall M Mapp, appBodyL M Mapp -> Term.

Inductive BetaStep : Term -> Term -> Prop :=
  Beta M Mapp Mabs : BetaStep M (lower M Mapp Mabs).

Goal forall M N, BetaStep M N -> True.
intros M N H.
inversion H as (P,Mapp,Mabs,H0,H1).
clear Mapp Mabs H0 H1.
exact Logic.I.
Qed.

(* Up to September 2014, H0 below was renamed called H1 because of a collision
   with the automaticallly generated names for equations.
   (example taken from CoLoR) *)

Inductive term := Var | Fun : term -> term -> term.
Inductive lt : term -> term -> Prop :=
  mpo f g ss ts : lt Var (Fun f ts) -> lt (Fun f ss) (Fun g ts).

Goal forall f g ss ts, lt (Fun f ss) (Fun g ts) -> lt Var (Fun f ts).
intros.
inversion H as (f',g',ss',ts',H0).
exact H0.
Qed.
