(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Corelib Require Import Prelude.

Set Universe Polymorphism.

Reserved Notation "x ~ y" (at level 70, no associativity).

Inductive obseq@{α;u} (A:Univ@{α;u}) (x:A) : A -> SProp :=
    obseq_refl : x ~ x

where "x ~ y" := (@obseq _ x y) : type_scope.

Arguments obseq {A} x _.
Arguments obseq_refl {A x} , [A] x.

Instance obseq_Has_refl@{α;l} : Has_refl@{α SProp;l Set} (@obseq) :=
  fun A x => obseq_refl.

Instance obseq_Has_J_elim_SProp@{α;l} : Has_J@{α SProp SProp;l Set Set} (@obseq) _
  := @obseq_sind.

Hint Resolve obseq_Has_J_elim_SProp : rewrite_instances.

Instance obseq_Has_Leibniz_elim_SProp@{α;l} : Has_Leibniz@{α SProp SProp;l Set Set} (@obseq)
  := fun A x P t y e => @obseq_sind A x (fun x _ => P x) t y e.

Hint Resolve obseq_Has_Leibniz_elim_SProp : rewrite_instances.

Instance obseq_Has_Leibniz_r_elim_SProp@{α;l +} : Has_Leibniz_r@{α SProp SProp;l Set Set} (@obseq)
  := fun A x P t y e => @obseq_sind A x (fun x _ => P x) t y (sym@{α SProp;l Set} e).

Hint Resolve obseq_Has_Leibniz_r_elim_SProp : rewrite_instances.

Parameter cast@{α;u u' | u<u'} : forall (A B : Univ@{α;u}), obseq@{Type;u'} A B -> A -> B.

Notation "e # a" := (cast _ _ e a) (at level 55, only parsing).

Instance obseq_Has_Leibniz_elim@{α β;l l' +} : Has_Leibniz@{α SProp β;l Set l'} (@obseq) :=
 { leibniz := fun A x P px y e => cast (P x) (P y) (ap P e) px}.

Hint Resolve obseq_Has_Leibniz_elim : rewrite_instances.

Instance obseq_Has_Leibniz_r_elim@{α β;l l' +} : Has_Leibniz_r@{α SProp β;l Set l'} (@obseq) :=
 { leibniz_r := fun A x P px y e => cast (P x) (P y) (ap P (sym e)) px}.

Hint Resolve obseq_Has_Leibniz_r_elim : rewrite_instances.


(* Having the instances on a generic equality :forall A : Type@{s;l}, A -> A -> Type@{s';l'} prevents
 the carriers universe from being irrelevant. Could we move Has_refl to be on a specific (@eq A)? *)
Definition obseq_apd@{sa sb; la lb}
    {A : Univ@{sa;la}} {a} (P : forall b : A, a ~ b -> Univ@{sb ; lb})
    (b : A) (e : a ~ b) : @obseq _ (P a (refl A a)) (P b e) :=
    J_eliminator@{sa SProp SProp;la 0 0} _ a (fun b e => @obseq@{Type;lb+1} _ (P a (refl _ _)) (P b e)) (refl _ _) b e.

Instance obseq_Has_J_elim@{α β;l l'} : Has_J@{α SProp β;l l l'} (@obseq) _ :=
  fun A a P t b e => cast (P a (refl _ _)) (P b e) (obseq_apd@{α β ;l l'} P b e) t.

Hint Resolve obseq_Has_J_elim : rewrite_instances.

Lemma test {A:Type} (a b : A) (P : A -> Type) : a ~ b -> P a -> P b.
Proof.
  intros e Pa. rewrite <- e. auto.
Defined.

Lemma test2 {A:Type} (a b : A) (P : A -> Type) : a ~ b -> P a -> P b.
Proof.
  intros e Pa. symmetry in e. rewrite e. auto.
Defined.
