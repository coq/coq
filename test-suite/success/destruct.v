(* Submitted by Robert Schneck *)

Parameters A B C D : Prop.
Axiom X : A -> B -> C /\ D.

Lemma foo : A -> B -> C.
Proof.
intros.
destruct X. (* Should find axiom X and should handle arguments of X *)
assumption.
assumption.
assumption.
Qed.

(* Simplification of bug 711 *)

Parameter f : true = false.
Goal let p := f in True.
intro p.
set (b := true) in *.
(* Check that it doesn't fail with an anomaly *)
(* Ultimately, adapt destruct to make it succeeding *)
try destruct b.
Abort.

(* Used to fail with error "n is used in conclusion" before revision 9447 *)

Goal forall n, n = S n.
induction S.
Abort.

(* Check that elimination with remaining evars do not raise an bad
   error message *)

Theorem Refl : forall P, P <-> P. tauto. Qed.
Goal True.
case Refl || ecase Refl.
Abort.


(* Submitted by B. Baydemir (bug #1882) *)

Require Import List.

Definition alist R := list (nat * R)%type.

Section Properties.
  Variable A : Type.
  Variable a : A.
  Variable E : alist A.

  Lemma silly : E = E.
  Proof.
    clear. induction E.  (* this fails. *)
  Abort.

End Properties.

(* This used not to work before revision 11944 *)

Goal forall P:(forall n, 0=n -> Prop), forall H: 0=0, P 0 H.
destruct H.
Abort.

(* The calls to "destruct" below did not work before revision 12356 *)

Variable A0:Type.
Variable P:A0->Type.
Require Import JMeq.
Goal forall a b (p:P a) (q:P b),
  forall H:a = b, eq_rect a P p b H = q -> JMeq (existT _ a p) (existT _ b q).
intros.
destruct H.
destruct H0.
reflexivity.
Qed.

(* These did not work before 8.4 *)

Goal (exists x, x=0) -> True.
destruct 1 as (_,_); exact I.
Abort.

Goal (exists x, x=0 /\ True) -> True.
destruct 1 as (_,(_,H)); exact H.
Abort.

Goal (exists x, x=0 /\ True) -> True.
destruct 1 as (_,(_,x)); exact x.
Abort.

