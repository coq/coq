(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Finite sets library.
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

Require Import Orders BoolOrder PeanoNat POrderedType BinNat BinInt
 RelationPairs EqualitiesFacts.
Require Import Ascii String.

(** * Examples of Ordered Type structures. *)


(** Ordered Type for [bool], [nat], [Positive], [N], [Z], [ascii], [string] with the usual or lexicographic order. *)

Module Bool_as_OT := BoolOrder.BoolOrd.
Module Nat_as_OT := PeanoNat.Nat.
Module Positive_as_OT := BinPos.Pos.
Module N_as_OT := BinNat.N.
Module Z_as_OT := BinInt.Z.

(** An OrderedType can now directly be seen as a DecidableType *)

Module OT_as_DT (O:OrderedType) <: DecidableType := O.

(** (Usual) Decidable Type for [bool], [nat], [positive], [N], [Z] *)

Module Bool_as_DT <: UsualDecidableType := Bool_as_OT.
Module Nat_as_DT <: UsualDecidableType := Nat_as_OT.
Module Positive_as_DT <: UsualDecidableType := Positive_as_OT.
Module N_as_DT <: UsualDecidableType := N_as_OT.
Module Z_as_DT <: UsualDecidableType := Z_as_OT.



(** From two ordered types, we can build a new OrderedType
   over their cartesian product, using the lexicographic order. *)

Module PairOrderedType(O1 O2:OrderedType) <: OrderedType.
 Include PairDecidableType O1 O2.

 Definition lt :=
   (relation_disjunction (O1.lt @@1) (O1.eq * O2.lt))%signature.

#[global]
 Instance lt_strorder : StrictOrder lt.
 Proof.
 split.
 - (* irreflexive *)
   intros (x1,x2); compute. destruct 1.
   + apply (StrictOrder_Irreflexive x1); auto.
   + apply (StrictOrder_Irreflexive x2); intuition.
 - (* transitive *)
   intros (x1,x2) (y1,y2) (z1,z2). compute. intuition.
   + left; etransitivity; eauto.
   + left. setoid_replace z1 with y1; auto with relations.
   + left; setoid_replace x1 with y1; auto with relations.
   + right; split; etransitivity; eauto.
 Qed.

#[global]
 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
 compute.
 intros (x1,x2) (x1',x2') (X1,X2) (y1,y2) (y1',y2') (Y1,Y2).
 rewrite X1,X2,Y1,Y2; intuition.
 Qed.

 Definition compare x y :=
  match O1.compare (fst x) (fst y) with
   | Eq => O2.compare (snd x) (snd y)
   | Lt => Lt
   | Gt => Gt
  end.

 Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
 Proof.
 intros (x1,x2) (y1,y2); unfold compare; simpl.
 destruct (O1.compare_spec x1 y1); try (constructor; compute; auto).
 destruct (O2.compare_spec x2 y2); constructor; compute; auto with relations.
 Qed.

End PairOrderedType.

(** Even if [positive] can be seen as an ordered type with respect to the
  usual order (see above), we can also use a lexicographic order over bits
  (lower bits are considered first). This is more natural when using
  [positive] as indexes for sets or maps (see MSetPositive). *)

Local Open Scope positive.

Module PositiveOrderedTypeBits <: UsualOrderedType.
  Definition t:=positive.
  Include HasUsualEq <+ UsualIsEq.
  Definition eqb := Pos.eqb.
  Definition eqb_eq := Pos.eqb_eq.
  Include HasEqBool2Dec.

  Fixpoint bits_lt (p q:positive) : Prop :=
   match p, q with
   | xH, xI _ => True
   | xH, _ => False
   | xO p, xO q => bits_lt p q
   | xO _, _ => True
   | xI p, xI q => bits_lt p q
   | xI _, _ => False
   end.

  Definition lt:=bits_lt.

  Lemma bits_lt_antirefl : forall x : positive, ~ bits_lt x x.
  Proof.
   induction x; simpl; auto.
  Qed.

  Lemma bits_lt_trans :
    forall x y z : positive, bits_lt x y -> bits_lt y z -> bits_lt x z.
  Proof.
   induction x; destruct y,z; simpl; eauto; intuition.
  Qed.

#[global]
  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
   intros x x' Hx y y' Hy. rewrite Hx, Hy; intuition.
  Qed.

#[global]
  Instance lt_strorder : StrictOrder lt.
  Proof.
   split; [ exact bits_lt_antirefl | exact bits_lt_trans ].
  Qed.

  Fixpoint compare x y :=
    match x, y with
      | x~1, y~1 => compare x y
      | _~1, _ => Gt
      | x~0, y~0 => compare x y
      | _~0, _ => Lt
      | 1, _~1 => Lt
      | 1, 1 => Eq
      | 1, _~0 => Gt
    end.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
   unfold eq, lt.
   induction x; destruct y; try constructor; simpl; auto.
   - destruct (IHx y); subst; auto.
   - destruct (IHx y); subst; auto.
  Qed.

End PositiveOrderedTypeBits.

Module Ascii_as_OT <: UsualOrderedType.
  Definition t := ascii.
  Include HasUsualEq <+ UsualIsEq.
  Definition eqb := Ascii.eqb.
  Definition eqb_eq := Ascii.eqb_eq.
  Include HasEqBool2Dec.

  Definition compare (a b : ascii) := N_as_OT.compare (N_of_ascii a) (N_of_ascii b).
  Definition lt (a b : ascii) := N_as_OT.lt (N_of_ascii a) (N_of_ascii b).

#[global]
  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    intros x x' Hx y y' Hy. rewrite Hx, Hy; intuition.
  Qed.

#[global]
  Instance lt_strorder : StrictOrder lt.
  Proof.
    split; unfold lt; [ intro | intros ??? ]; eapply N_as_OT.lt_strorder.
  Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros x y; unfold eq, lt, compare.
    destruct (N_as_OT.compare_spec (N_of_ascii x) (N_of_ascii y)) as [H|H|H]; constructor; try assumption.
    now rewrite <- (ascii_N_embedding x), <- (ascii_N_embedding y), H.
  Qed.
End Ascii_as_OT.

(** [String] is an ordered type with respect to the usual lexical order. *)

Module String_as_OT <: UsualOrderedType.
  Definition t := string.
  Include HasUsualEq <+ UsualIsEq.
  Definition eqb := String.eqb.
  Definition eqb_eq := String.eqb_eq.
  Include HasEqBool2Dec.

  Fixpoint compare (a b : string)
    := match a, b with
       | EmptyString, EmptyString => Eq
       | EmptyString, _ => Lt
       | String _ _, EmptyString => Gt
       | String a_head a_tail, String b_head b_tail =>
         match Ascii_as_OT.compare a_head b_head with
         | Lt => Lt
         | Gt => Gt
         | Eq => compare a_tail b_tail
         end
       end.

  Definition lt (a b : string) := compare a b = Lt.

#[global]
  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    intros x x' Hx y y' Hy. rewrite Hx, Hy; intuition.
  Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    unfold eq, lt.
    induction x as [|x xs IHxs], y as [|y ys]; cbn [compare]; try constructor; cbn [compare]; try reflexivity.
    specialize (IHxs ys).
    destruct (Ascii_as_OT.compare x y) eqn:H; [ destruct IHxs; constructor | constructor | constructor ]; cbn [compare].
    all: destruct (Ascii_as_OT.compare_spec y x), (Ascii_as_OT.compare_spec x y); cbv [Ascii_as_OT.eq] in *; try congruence; subst.
    all: exfalso; eapply irreflexivity; (idtac + etransitivity); eassumption.
  Qed.

#[global]
  Instance lt_strorder : StrictOrder lt.
  Proof.
    split; unfold lt; [ intro x | intros x y z ]; unfold complement.
    { induction x as [|x xs IHxs]; cbn [compare]; [ congruence | ].
      destruct (Ascii_as_OT.compare x x) eqn:H; try congruence.
      exfalso; eapply irreflexivity; eassumption. }
    { revert x y z.
      induction x as [|x xs IHxs], y as [|y ys], z as [|z zs]; cbn [compare]; try congruence.
      specialize (IHxs ys zs).
      destruct (Ascii_as_OT.compare x y) eqn:Hxy, (Ascii_as_OT.compare y z) eqn:Hyz, (Ascii_as_OT.compare x z) eqn:Hxz;
        try intuition (congruence || eauto).
      all: destruct (Ascii_as_OT.compare_spec x y), (Ascii_as_OT.compare_spec y z), (Ascii_as_OT.compare_spec x z);
        try discriminate.
      all: unfold Ascii_as_OT.eq in *; subst.
      all: exfalso; eapply irreflexivity; (idtac + etransitivity); (idtac + etransitivity); eassumption. }
  Qed.
End String_as_OT.
