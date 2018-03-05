(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * An light axiomatization of integers (used in MSetAVL). *)

(** We define a signature for an integer datatype based on [Z].
    The goal is to allow a switch after extraction to ocaml's
    [big_int] or even [int] when finiteness isn't a problem
    (typically : when mesuring the height of an AVL tree).
*)

Require Import BinInt.
Delimit Scope Int_scope with I.
Local Open Scope Int_scope.

(** * A specification of integers *)

Module Type Int.

  Parameter t : Set.
  Bind Scope Int_scope with t.

  Parameter i2z : t -> Z.

  Parameter _0 : t.
  Parameter _1 : t.
  Parameter _2 : t.
  Parameter _3 : t.
  Parameter add : t -> t -> t.
  Parameter opp : t -> t.
  Parameter sub : t -> t -> t.
  Parameter mul : t -> t -> t.
  Parameter max : t -> t -> t.

  Notation "0" := _0 : Int_scope.
  Notation "1" := _1 : Int_scope.
  Notation "2" := _2 : Int_scope.
  Notation "3" := _3 : Int_scope.
  Infix "+" := add : Int_scope.
  Infix "-" := sub : Int_scope.
  Infix "*" := mul : Int_scope.
  Notation "- x" := (opp x) : Int_scope.

  (** For logical relations, we can rely on their counterparts in Z,
      since they don't appear after extraction. Moreover, using tactics
      like omega is easier this way. *)

  Notation "x == y" := (i2z x = i2z y)
    (at level 70, y at next level, no associativity) : Int_scope.
  Notation "x <= y" := (i2z x <= i2z y)%Z : Int_scope.
  Notation "x < y" := (i2z x < i2z y)%Z : Int_scope.
  Notation "x >= y" := (i2z x >= i2z y)%Z : Int_scope.
  Notation "x > y" := (i2z x > i2z y)%Z : Int_scope.
  Notation "x <= y <= z" := (x <= y /\ y <= z) : Int_scope.
  Notation "x <= y < z" := (x <= y /\ y < z) : Int_scope.
  Notation "x < y < z" := (x < y /\ y < z) : Int_scope.
  Notation "x < y <= z" := (x < y /\ y <= z) : Int_scope.

  (** Informative comparisons. *)

  Axiom eqb : t -> t -> bool.
  Axiom ltb : t -> t -> bool.
  Axiom leb : t -> t -> bool.

  Infix "=?" := eqb.
  Infix "<?" := ltb.
  Infix "<=?" := leb.

  (** For compatibility, some decidability fonctions (informative). *)

  Axiom gt_le_dec : forall x y : t, {x > y} + {x <= y}.
  Axiom ge_lt_dec :  forall x y : t, {x >= y} + {x < y}.
  Axiom eq_dec : forall x y : t, { x == y } + {~ x==y }.

  (** Specifications *)

  (** First, we ask [i2z] to be injective. Said otherwise, our ad-hoc equality
      [==] and the generic [=] are in fact equivalent. We define [==]
      nonetheless since the translation to [Z] for using automatic tactic
      is easier. *)

  Axiom i2z_eq : forall n p : t, n == p -> n = p.

   (** Then, we express the specifications of the above parameters using their
       Z counterparts. *)

  Axiom i2z_0 : i2z _0 = 0%Z.
  Axiom i2z_1 : i2z _1 = 1%Z.
  Axiom i2z_2 : i2z _2 = 2%Z.
  Axiom i2z_3 : i2z _3 = 3%Z.
  Axiom i2z_add : forall n p, i2z (n + p) = (i2z n + i2z p)%Z.
  Axiom i2z_opp : forall n, i2z (-n) = (-i2z n)%Z.
  Axiom i2z_sub : forall n p, i2z (n - p) = (i2z n - i2z p)%Z.
  Axiom i2z_mul : forall n p, i2z (n * p) = (i2z n * i2z p)%Z.
  Axiom i2z_max : forall n p, i2z (max n p) = Z.max (i2z n) (i2z p).
  Axiom i2z_eqb : forall n p, eqb n p = Z.eqb (i2z n) (i2z p).
  Axiom i2z_ltb : forall n p, ltb n p = Z.ltb (i2z n) (i2z p).
  Axiom i2z_leb : forall n p, leb n p = Z.leb (i2z n) (i2z p).

End Int.


(** * Facts and  tactics using [Int] *)

Module MoreInt (Import I:Int).
  Local Notation int := I.t.

  Lemma eqb_eq n p : (n =? p) = true <-> n == p.
  Proof.
   now rewrite i2z_eqb, Z.eqb_eq.
  Qed.

  Lemma eqb_neq n p : (n =? p) = false <-> ~(n == p).
  Proof.
   rewrite <- eqb_eq. destruct (n =? p); intuition.
  Qed.

  Lemma ltb_lt n p : (n <? p) = true <-> n < p.
  Proof.
   now rewrite i2z_ltb, Z.ltb_lt.
  Qed.

  Lemma ltb_nlt n p : (n <? p) = false <-> ~(n < p).
  Proof.
   rewrite <- ltb_lt. destruct (n <? p); intuition.
  Qed.

  Lemma leb_le n p : (n <=? p) = true <-> n <= p.
  Proof.
   now rewrite i2z_leb, Z.leb_le.
  Qed.

  Lemma leb_nle n p : (n <=? p) = false <-> ~(n <= p).
  Proof.
   rewrite <- leb_le. destruct (n <=? p); intuition.
  Qed.

  (** A magic (but costly) tactic that goes from [int] back to the [Z]
      friendly world ... *)

  Hint Rewrite ->
    i2z_0 i2z_1 i2z_2 i2z_3 i2z_add i2z_opp i2z_sub i2z_mul i2z_max
    i2z_eqb i2z_ltb i2z_leb : i2z.

  Ltac i2z := match goal with
    | H : ?a = ?b |- _ =>
      generalize (f_equal i2z H);
	try autorewrite with i2z; clear H; intro H; i2z
    | |- ?a = ?b =>
      apply (i2z_eq a b); try autorewrite with i2z; i2z
    | H : _ |- _ => progress autorewrite with i2z in H; i2z
    | _ => try autorewrite with i2z
  end.

  (** A reflexive version of the [i2z] tactic *)

  (** this [i2z_refl] is actually weaker than [i2z]. For instance, if a
      [i2z] is buried deep inside a subterm, [i2z_refl] may miss it.
      See also the limitation about [Set] or [Type] part below.
      Anyhow, [i2z_refl] is enough for applying [romega]. *)

  Ltac i2z_gen := match goal with
    | |- ?a = ?b => apply (i2z_eq a b); i2z_gen
    | H : ?a = ?b |- _ =>
       generalize (f_equal i2z H); clear H; i2z_gen
    | H : eq (A:=Z) ?a ?b |- _ => revert H; i2z_gen
    | H : Z.lt ?a ?b |- _ => revert H; i2z_gen
    | H : Z.le ?a ?b |- _ => revert H; i2z_gen
    | H : Z.gt ?a ?b |- _ => revert H; i2z_gen
    | H : Z.ge ?a ?b |- _ => revert H; i2z_gen
    | H : _ -> ?X |- _ =>
      (* A [Set] or [Type] part cannot be dealt with easily
         using the [ExprP] datatype. So we forget it, leaving
         a goal that can be weaker than the original. *)
      match type of X with
       | Type => clear H; i2z_gen
       | Prop => revert H; i2z_gen
      end
    | H : _ <-> _ |- _ => revert H; i2z_gen
    | H : _ /\ _ |- _ => revert H; i2z_gen
    | H : _ \/ _ |- _ => revert H; i2z_gen
    | H : ~ _ |- _ => revert H; i2z_gen
    | _ => idtac
   end.

  Inductive ExprI : Set :=
    | EI0 : ExprI
    | EI1 : ExprI
    | EI2 : ExprI
    | EI3 : ExprI
    | EIadd : ExprI -> ExprI -> ExprI
    | EIopp : ExprI -> ExprI
    | EIsub : ExprI -> ExprI -> ExprI
    | EImul : ExprI -> ExprI -> ExprI
    | EImax : ExprI -> ExprI -> ExprI
    | EIraw : int -> ExprI.

  Inductive ExprZ : Set :=
    | EZadd : ExprZ -> ExprZ -> ExprZ
    | EZopp : ExprZ -> ExprZ
    | EZsub : ExprZ -> ExprZ -> ExprZ
    | EZmul : ExprZ -> ExprZ -> ExprZ
    | EZmax : ExprZ -> ExprZ -> ExprZ
    | EZofI : ExprI -> ExprZ
    | EZraw : Z -> ExprZ.

  Inductive ExprP : Type :=
    | EPeq : ExprZ -> ExprZ -> ExprP
    | EPlt : ExprZ -> ExprZ -> ExprP
    | EPle : ExprZ -> ExprZ -> ExprP
    | EPgt : ExprZ -> ExprZ -> ExprP
    | EPge : ExprZ -> ExprZ -> ExprP
    | EPimpl : ExprP -> ExprP -> ExprP
    | EPequiv : ExprP -> ExprP -> ExprP
    | EPand : ExprP -> ExprP -> ExprP
    | EPor : ExprP -> ExprP -> ExprP
    | EPneg : ExprP -> ExprP
    | EPraw : Prop -> ExprP.

  (** [int] to [ExprI] *)

  Ltac i2ei trm :=
    match constr:(trm) with
      | 0 => constr:(EI0)
      | 1 => constr:(EI1)
      | 2 => constr:(EI2)
      | 3 => constr:(EI3)
      | ?x + ?y => let ex := i2ei x with ey := i2ei y in constr:(EIadd ex ey)
      | ?x - ?y => let ex := i2ei x with ey := i2ei y in constr:(EIsub ex ey)
      | ?x * ?y => let ex := i2ei x with ey := i2ei y in constr:(EImul ex ey)
      | max ?x ?y => let ex := i2ei x with ey := i2ei y in constr:(EImax ex ey)
      | - ?x => let ex := i2ei x in constr:(EIopp ex)
      | ?x => constr:(EIraw x)
    end

  (** [Z] to [ExprZ] *)

    with z2ez trm :=
    match constr:(trm) with
      | (?x + ?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EZadd ex ey)
      | (?x - ?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EZsub ex ey)
      | (?x * ?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EZmul ex ey)
      | (Z.max ?x ?y) => let ex := z2ez x with ey := z2ez y in constr:(EZmax ex ey)
      | (- ?x)%Z =>  let ex := z2ez x in constr:(EZopp ex)
      | i2z ?x => let ex := i2ei x in constr:(EZofI ex)
      | ?x => constr:(EZraw x)
    end.

  (** [Prop] to [ExprP] *)

  Ltac p2ep trm :=
    match constr:(trm) with
      | (?x <-> ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPequiv ex ey)
      | (?x -> ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPimpl ex ey)
      | (?x /\ ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPand ex ey)
      | (?x \/ ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPor ex ey)
      | (~ ?x) => let ex := p2ep x in constr:(EPneg ex)
      | (eq (A:=Z) ?x ?y) => let ex := z2ez x with ey := z2ez y in constr:(EPeq ex ey)
      | (?x < ?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPlt ex ey)
      | (?x <= ?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPle ex ey)
      | (?x > ?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPgt ex ey)
      | (?x >= ?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPge ex ey)
      | ?x =>  constr:(EPraw x)
    end.

  (** [ExprI] to [int] *)

  Fixpoint ei2i (e:ExprI) : int :=
    match e with
      | EI0 => 0
      | EI1 => 1
      | EI2 => 2
      | EI3 => 3
      | EIadd e1 e2 => (ei2i e1)+(ei2i e2)
      | EIsub e1 e2 => (ei2i e1)-(ei2i e2)
      | EImul e1 e2 => (ei2i e1)*(ei2i e2)
      | EImax e1 e2 => max (ei2i e1) (ei2i e2)
      | EIopp e => -(ei2i e)
      | EIraw i => i
    end.

  (** [ExprZ] to [Z] *)

  Fixpoint ez2z (e:ExprZ) : Z :=
    match e with
      | EZadd e1 e2 => ((ez2z e1)+(ez2z e2))%Z
      | EZsub e1 e2 => ((ez2z e1)-(ez2z e2))%Z
      | EZmul e1 e2 => ((ez2z e1)*(ez2z e2))%Z
      | EZmax e1 e2 => Z.max (ez2z e1) (ez2z e2)
      | EZopp e => (-(ez2z e))%Z
      | EZofI e => i2z (ei2i e)
      | EZraw z => z
    end.

  (** [ExprP] to [Prop] *)

  Fixpoint ep2p (e:ExprP) : Prop :=
    match e with
      | EPeq e1 e2 => (ez2z e1) = (ez2z e2)
      | EPlt e1 e2 => ((ez2z e1)<(ez2z e2))%Z
      | EPle e1 e2 => ((ez2z e1)<=(ez2z e2))%Z
      | EPgt e1 e2 => ((ez2z e1)>(ez2z e2))%Z
      | EPge e1 e2 => ((ez2z e1)>=(ez2z e2))%Z
      | EPimpl e1 e2 => (ep2p e1) -> (ep2p e2)
      | EPequiv e1 e2 => (ep2p e1) <-> (ep2p e2)
      | EPand e1 e2 => (ep2p e1) /\ (ep2p e2)
      | EPor e1 e2 => (ep2p e1) \/ (ep2p e2)
      | EPneg e => ~ (ep2p e)
      | EPraw p => p
    end.

  (** [ExprI] (supposed under a [i2z]) to a simplified [ExprZ] *)

  Fixpoint norm_ei (e:ExprI) : ExprZ :=
    match e with
      | EI0 => EZraw (0%Z)
      | EI1 => EZraw (1%Z)
      | EI2 => EZraw (2%Z)
      | EI3 => EZraw (3%Z)
      | EIadd e1 e2 => EZadd (norm_ei e1) (norm_ei e2)
      | EIsub e1 e2 => EZsub (norm_ei e1) (norm_ei e2)
      | EImul e1 e2 => EZmul (norm_ei e1) (norm_ei e2)
      | EImax e1 e2 => EZmax (norm_ei e1) (norm_ei e2)
      | EIopp e => EZopp (norm_ei e)
      | EIraw i => EZofI (EIraw i)
    end.

  (** [ExprZ] to a simplified [ExprZ] *)

  Fixpoint norm_ez (e:ExprZ) : ExprZ :=
    match e with
      | EZadd e1 e2 => EZadd (norm_ez e1) (norm_ez e2)
      | EZsub e1 e2 => EZsub (norm_ez e1) (norm_ez e2)
      | EZmul e1 e2 => EZmul (norm_ez e1) (norm_ez e2)
      | EZmax e1 e2 => EZmax (norm_ez e1) (norm_ez e2)
      | EZopp e => EZopp (norm_ez e)
      | EZofI e =>  norm_ei e
      | EZraw z => EZraw z
    end.

  (** [ExprP] to a simplified [ExprP] *)

  Fixpoint norm_ep (e:ExprP) : ExprP :=
    match e with
      | EPeq e1 e2 => EPeq (norm_ez e1) (norm_ez e2)
      | EPlt e1 e2 => EPlt (norm_ez e1) (norm_ez e2)
      | EPle e1 e2 => EPle (norm_ez e1) (norm_ez e2)
      | EPgt e1 e2 => EPgt (norm_ez e1) (norm_ez e2)
      | EPge e1 e2 => EPge (norm_ez e1) (norm_ez e2)
      | EPimpl e1 e2 => EPimpl (norm_ep e1) (norm_ep e2)
      | EPequiv e1 e2 => EPequiv (norm_ep e1) (norm_ep e2)
      | EPand e1 e2 => EPand (norm_ep e1) (norm_ep e2)
      | EPor e1 e2 => EPor (norm_ep e1) (norm_ep e2)
      | EPneg e => EPneg (norm_ep e)
      | EPraw p => EPraw p
    end.

  Lemma norm_ei_correct (e:ExprI) : ez2z (norm_ei e) = i2z (ei2i e).
  Proof.
    induction e; simpl; i2z; auto; try congruence.
  Qed.

  Lemma norm_ez_correct (e:ExprZ) : ez2z (norm_ez e) = ez2z e.
  Proof.
    induction e; simpl; i2z; auto; try congruence; apply norm_ei_correct.
  Qed.

  Lemma norm_ep_correct (e:ExprP) : ep2p (norm_ep e) <-> ep2p e.
  Proof.
    induction e; simpl; rewrite ?norm_ez_correct; intuition.
  Qed.

  Lemma norm_ep_correct2 (e:ExprP) : ep2p (norm_ep e) -> ep2p e.
  Proof.
    intros; destruct (norm_ep_correct e); auto.
  Qed.

  Ltac i2z_refl :=
    i2z_gen;
    match goal with |- ?t =>
      let e := p2ep t in
      change (ep2p e); apply norm_ep_correct2; simpl
    end.

  (* i2z_refl can be replaced below by (simpl in *; i2z).
     The reflexive version improves compilation of AVL files by about 15%  *)

End MoreInt.



(** * An implementation of [Int] *)

(** It's always nice to know that our [Int] interface is realizable :-) *)

Module Z_as_Int <: Int.
  Local Open Scope Z_scope.
  Definition t := Z.
  Definition _0 := 0.
  Definition _1 := 1.
  Definition _2 := 2.
  Definition _3 := 3.
  Definition add := Z.add.
  Definition opp := Z.opp.
  Definition sub := Z.sub.
  Definition mul := Z.mul.
  Definition max := Z.max.
  Definition eqb := Z.eqb.
  Definition ltb := Z.ltb.
  Definition leb := Z.leb.

  Definition eq_dec := Z.eq_dec.
  Definition gt_le_dec i j : {i > j} + { i <= j }.
  Proof.
    generalize (Z.ltb_spec j i).
    destruct (j <? i); [left|right]; inversion H; trivial.
    now apply Z.lt_gt.
  Defined.
  Definition ge_lt_dec i j : {i >= j} + { i < j }.
  Proof.
    generalize (Z.ltb_spec i j).
    destruct (i <? j); [right|left]; inversion H; trivial.
    now apply Z.le_ge.
  Defined.

  Definition i2z : t -> Z := fun n => n.
  Lemma i2z_eq n p : i2z n = i2z p -> n = p. Proof. trivial. Qed.
  Lemma i2z_0 : i2z _0 = 0.  Proof. reflexivity. Qed.
  Lemma i2z_1 : i2z _1 = 1.  Proof. reflexivity. Qed.
  Lemma i2z_2 : i2z _2 = 2.  Proof. reflexivity. Qed.
  Lemma i2z_3 : i2z _3 = 3.  Proof. reflexivity. Qed.
  Lemma i2z_add n p : i2z (n + p) = i2z n + i2z p.
  Proof. reflexivity. Qed.
  Lemma i2z_opp n : i2z (- n) = - i2z n.
  Proof. reflexivity. Qed.
  Lemma i2z_sub n p : i2z (n - p) = i2z n - i2z p.
  Proof. reflexivity. Qed.
  Lemma i2z_mul n p : i2z (n * p) = i2z n * i2z p.
  Proof. reflexivity. Qed.
  Lemma i2z_max n p : i2z (max n p) = Z.max (i2z n) (i2z p).
  Proof. reflexivity. Qed.
  Lemma i2z_eqb n p : eqb n p = Z.eqb (i2z n) (i2z p).
  Proof. reflexivity. Qed.
  Lemma i2z_leb n p : leb n p = Z.leb (i2z n) (i2z p).
  Proof. reflexivity. Qed.
  Lemma i2z_ltb n p : ltb n p = Z.ltb (i2z n) (i2z p).
  Proof. reflexivity. Qed.

  (** Compatibility notations for Coq v8.4 *)
  Notation plus := add (only parsing).
  Notation minus := sub (only parsing).
  Notation mult := mul (only parsing).
End Z_as_Int.
