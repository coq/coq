(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * Relations over pairs *)


Require Import Relations Morphisms.

(* NB: This should be system-wide someday, but for that we need to
    fix the simpl tactic, since "simpl fst" would be refused for
    the moment.

Implicit Arguments fst [[A] [B]].
Implicit Arguments snd [[A] [B]].
Implicit Arguments pair [[A] [B]].

/NB *)

Local Notation Fst := (@fst _ _).
Local Notation Snd := (@snd _ _).

Arguments Scope relation_conjunction
 [type_scope signature_scope signature_scope].
Arguments Scope relation_equivalence
 [type_scope signature_scope signature_scope].
Arguments Scope subrelation [type_scope signature_scope signature_scope].
Arguments Scope Reflexive [type_scope signature_scope].
Arguments Scope Irreflexive [type_scope signature_scope].
Arguments Scope Symmetric [type_scope signature_scope].
Arguments Scope Transitive [type_scope signature_scope].
Arguments Scope PER [type_scope signature_scope].
Arguments Scope Equivalence [type_scope signature_scope].
Arguments Scope StrictOrder [type_scope signature_scope].

Generalizable Variables A B RA RB Ri Ro f.

(** Any function from [A] to [B] allow to obtain a relation over [A]
    out of a relation over [B]. *)

Definition RelCompFun {A B}(R:relation B)(f:A->B) : relation A :=
 fun a a' => R (f a) (f a').

Infix "@@" := RelCompFun (at level 30, right associativity) : signature_scope.

Notation "R @@1" := (R @@ Fst)%signature (at level 30) : signature_scope.
Notation "R @@2" := (R @@ Snd)%signature (at level 30) : signature_scope.

(** We declare measures to the system using the [Measure] class.
   Otherwise the instances would easily introduce loops,
   never instantiating the [f] function.  *)

Class Measure {A B} (f : A -> B).

(** Standard measures. *)

Instance fst_measure : @Measure (A * B) A Fst.
Instance snd_measure : @Measure (A * B) B Snd.

(** We define a product relation over [A*B]: each components should
    satisfy the corresponding initial relation. *)

Definition RelProd {A B}(RA:relation A)(RB:relation B) : relation (A*B) :=
 relation_conjunction (RA @@1) (RB @@2).

Infix "*" := RelProd : signature_scope.

Section RelCompFun_Instances.
  Context {A B : Type} (R : relation B).

  Global Instance RelCompFun_Reflexive
    `(Measure A B f, Reflexive _ R) : Reflexive (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Symmetric
    `(Measure A B f, Symmetric _ R) : Symmetric (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Transitive
    `(Measure A B f, Transitive _ R) : Transitive (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Irreflexive
    `(Measure A B f, Irreflexive _ R) : Irreflexive (R@@f).
  Proof. firstorder. Qed.

  Global Instance RelCompFun_Equivalence
    `(Measure A B f, Equivalence _ R) : Equivalence (R@@f).

  Global Instance RelCompFun_StrictOrder
    `(Measure A B f, StrictOrder _ R) : StrictOrder (R@@f).

End RelCompFun_Instances.

Instance RelProd_Reflexive {A B}(RA:relation A)(RB:relation B)
 `(Reflexive _ RA, Reflexive _ RB) : Reflexive (RA*RB).
Proof. firstorder. Qed.

Instance RelProd_Symmetric {A B}(RA:relation A)(RB:relation B)
 `(Symmetric _ RA, Symmetric _ RB) : Symmetric (RA*RB).
Proof. firstorder. Qed.

Instance RelProd_Transitive {A B}(RA:relation A)(RB:relation B)
 `(Transitive _ RA, Transitive _ RB) : Transitive (RA*RB).
Proof. firstorder. Qed.

Instance RelProd_Equivalence {A B}(RA:relation A)(RB:relation B)
 `(Equivalence _ RA, Equivalence _ RB) : Equivalence (RA*RB).

Lemma FstRel_ProdRel {A B}(RA:relation A) :
 relation_equivalence (RA @@1) (RA*(fun _ _ : B => True)).
Proof. firstorder. Qed.

Lemma SndRel_ProdRel {A B}(RB:relation B) :
 relation_equivalence (RB @@2) ((fun _ _ : A =>True) * RB).
Proof. firstorder. Qed.

Instance FstRel_sub {A B} (RA:relation A)(RB:relation B):
 subrelation (RA*RB) (RA @@1).
Proof. firstorder. Qed.

Instance SndRel_sub {A B} (RA:relation A)(RB:relation B):
 subrelation (RA*RB) (RB @@2).
Proof. firstorder. Qed.

Instance pair_compat { A B } (RA:relation A)(RB:relation B) :
 Proper (RA==>RB==> RA*RB) (@pair _ _).
Proof. firstorder. Qed.

Instance fst_compat { A B } (RA:relation A)(RB:relation B) :
 Proper (RA*RB ==> RA) Fst.
Proof.
intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
Qed.

Instance snd_compat { A B } (RA:relation A)(RB:relation B) :
 Proper (RA*RB ==> RB) Snd.
Proof.
intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
Qed.

Instance RelCompFun_compat {A B}(f:A->B)(R : relation B)
 `(Proper _ (Ri==>Ri==>Ro) R) :
 Proper (Ri@@f==>Ri@@f==>Ro) (R@@f)%signature.
Proof. unfold RelCompFun; firstorder. Qed.

Hint Unfold RelProd RelCompFun.
Hint Extern 2 (RelProd _ _ _ _) => split.

