(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Properties of a binary relation [R] on type [A] *)

Section Rstar.
  
  Variable A : Type.  
  Variable R : A -> A -> Prop.  

  (** Definition of the reflexive-transitive closure [R*] of [R] *)
  (** Smallest reflexive [P] containing [R o P] *)

  Definition Rstar (x y:A) :=
    forall P:A -> A -> Prop,
      (forall u:A, P u u) -> (forall u v w:A, R u v -> P v w -> P u w) -> P x y.  
  
  Theorem Rstar_reflexive : forall x:A, Rstar x x.
  Proof.
    unfold Rstar. intros x P P_refl RoP. apply P_refl.
  Qed.

  Theorem Rstar_R : forall x y z:A, R x y -> Rstar y z -> Rstar x z.
  Proof.
    intros x y z R_xy Rstar_yz.
    unfold Rstar.
    intros P P_refl RoP. apply RoP with (v:=y).
      assumption.
      apply Rstar_yz; assumption.
  Qed.

  (** We conclude with transitivity of [Rstar] : *)

  Theorem Rstar_transitive :
    forall x y z:A, Rstar x y -> Rstar y z -> Rstar x z.
  Proof.
    intros x y z Rstar_xy; unfold Rstar in Rstar_xy.
    apply Rstar_xy; trivial.
    intros u v w R_uv fz Rstar_wz.
    apply Rstar_R with (y:=v); auto.
  Qed.

  (** Another characterization of [R*] *)
  (** Smallest reflexive [P] containing [R o R*] *)

  Definition Rstar' (x y:A) :=
    forall P:A -> A -> Prop,
      P x x -> (forall u:A, R x u -> Rstar u y -> P x y) -> P x y.  

  Theorem Rstar'_reflexive : forall x:A, Rstar' x x.
  Proof.
    unfold Rstar'; intros; assumption.
  Qed.
  
  Theorem Rstar'_R : forall x y z:A, R x z -> Rstar z y -> Rstar' x y.
  Proof.
    unfold Rstar'. intros x y z Rxz Rstar_zy P Pxx RoP.
    apply RoP with (u:=z); trivial.
  Qed.
  
  (** Equivalence of the two definitions: *)

  Theorem Rstar'_Rstar : forall x y:A, Rstar' x y -> Rstar x y.
  Proof.
    intros x z Rstar'_xz; unfold Rstar' in Rstar'_xz.
    apply Rstar'_xz.
      exact (Rstar_reflexive x).
      intro y; generalize x y z; exact Rstar_R.
  Qed.
  
  Theorem Rstar_Rstar' : forall x y:A, Rstar x y -> Rstar' x y.
  Proof.
    intros.
    apply H.
      exact Rstar'_reflexive.
      intros u v  w R_uv Rs'_vw. apply Rstar'_R with (z:=v).
        assumption.
        apply Rstar'_Rstar; assumption.
  Qed.

  (** Property of Commutativity of two relations *)
  
  Definition commut (A:Type) (R1 R2:A -> A -> Prop) :=
    forall x y:A,
      R1 y x -> forall z:A, R2 z y ->  exists2 y' : A, R2 y' x & R1 z y'.

End Rstar.
