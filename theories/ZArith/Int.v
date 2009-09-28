(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(** * An light axiomatization of integers (used in FSetAVL). *)

(** We define a signature for an integer datatype based on [Z].
    The goal is to allow a switch after extraction to ocaml's
    [big_int] or even [int] when finiteness isn't a problem
    (typically : when mesuring the height of an AVL tree).
*)

Require Import ZArith.
Delimit Scope Int_scope with I.


(** * a specification of integers *)

Module Type Int.

  Open Scope Int_scope.

  Parameter int : Set.

  Parameter i2z : int -> Z.
  Arguments Scope i2z [ Int_scope ].

  Parameter _0 : int.
  Parameter _1 : int.
  Parameter _2 : int.
  Parameter _3 : int.
  Parameter plus : int -> int -> int.
  Parameter opp : int -> int.
  Parameter minus : int -> int -> int.
  Parameter mult : int -> int -> int.
  Parameter max : int -> int -> int.

  Notation "0" := _0 : Int_scope.
  Notation "1" := _1 : Int_scope.
  Notation "2" := _2 : Int_scope.
  Notation "3" := _3 : Int_scope.
  Infix "+" := plus : Int_scope.
  Infix "-" := minus : Int_scope.
  Infix "*" := mult : Int_scope.
  Notation "- x" := (opp x) : Int_scope.

  (** For logical relations, we can rely on their counterparts in Z,
      since they don't appear after extraction. Moreover, using tactics
      like omega is easier this way. *)

  Notation "x == y" := (i2z x = i2z y)
    (at level 70, y at next level, no associativity) : Int_scope.
  Notation "x <= y" := (Zle (i2z x) (i2z y)): Int_scope.
  Notation "x < y" := (Zlt (i2z x) (i2z y)) : Int_scope.
  Notation "x >= y" := (Zge (i2z x) (i2z y)) : Int_scope.
  Notation "x > y" := (Zgt (i2z x) (i2z y)): Int_scope.
  Notation "x <= y <= z" := (x <= y /\ y <= z) : Int_scope.
  Notation "x <= y < z" := (x <= y /\ y < z) : Int_scope.
  Notation "x < y < z" := (x < y /\ y < z) : Int_scope.
  Notation "x < y <= z" := (x < y /\ y <= z) : Int_scope.

  (** Some decidability fonctions (informative). *)

  Axiom gt_le_dec : forall x y: int, {x > y} + {x <= y}.
  Axiom ge_lt_dec :  forall x y : int, {x >= y} + {x < y}.
  Axiom eq_dec : forall x y : int, { x == y } + {~ x==y }.

  (** Specifications *)

  (** First, we ask [i2z] to be injective. Said otherwise, our ad-hoc equality
      [==] and the generic [=] are in fact equivalent. We define [==]
      nonetheless since the translation to [Z] for using automatic tactic is easier. *)

  Axiom i2z_eq : forall n p : int, n == p -> n = p.

   (** Then, we express the specifications of the above parameters using their
       Z counterparts. *)

  Open Scope Z_scope.
  Axiom i2z_0 : i2z _0 = 0.
  Axiom i2z_1 : i2z _1 = 1.
  Axiom i2z_2 : i2z _2 = 2.
  Axiom i2z_3 : i2z _3 = 3.
  Axiom i2z_plus : forall n p, i2z (n + p) = i2z n + i2z p.
  Axiom i2z_opp : forall n, i2z (-n) = -i2z n.
  Axiom i2z_minus : forall n p, i2z (n - p) = i2z n - i2z p.
  Axiom i2z_mult : forall n p, i2z (n * p) = i2z n * i2z p.
  Axiom i2z_max : forall n p, i2z (max n p) = Zmax (i2z n) (i2z p).

End Int.


(** * Facts and  tactics using [Int] *)

Module MoreInt (I:Int).
  Import I.

  Open Scope Int_scope.

  (** A magic (but costly) tactic that goes from [int] back to the [Z]
      friendly world ... *)

  Hint Rewrite ->
    i2z_0 i2z_1 i2z_2 i2z_3 i2z_plus i2z_opp i2z_minus i2z_mult i2z_max : i2z.

  Ltac i2z := match goal with
		| H : (eq (A:=int) ?a ?b) |- _ =>
		  generalize (f_equal i2z H);
		    try autorewrite with i2z; clear H; intro H; i2z
		| |- (eq (A:=int) ?a ?b) => apply (i2z_eq a b); try autorewrite with i2z; i2z
		| H : _ |- _ => progress autorewrite with i2z in H; i2z
		| _ => try autorewrite with i2z
	      end.

  (** A reflexive version of the [i2z] tactic *)

  (** this [i2z_refl] is actually weaker than [i2z]. For instance, if a
      [i2z] is buried deep inside a subterm, [i2z_refl] may miss it.
      See also the limitation about [Set] or [Type] part below.
      Anyhow, [i2z_refl] is enough for applying [romega]. *)

  Ltac i2z_gen := match goal with
    | |- (eq (A:=int) ?a ?b) => apply (i2z_eq a b); i2z_gen
    | H : (eq (A:=int) ?a ?b) |- _ =>
       generalize (f_equal i2z H); clear H; i2z_gen
    | H : (eq (A:=Z) ?a ?b) |- _ => revert H; i2z_gen
    | H : (Zlt ?a ?b) |- _ => revert H; i2z_gen
    | H : (Zle ?a ?b) |- _ => revert H; i2z_gen
    | H : (Zgt ?a ?b) |- _ => revert H; i2z_gen
    | H : (Zge ?a ?b) |- _ => revert H; i2z_gen
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
    | EIplus : ExprI -> ExprI -> ExprI
    | EIopp : ExprI -> ExprI
    | EIminus : ExprI -> ExprI -> ExprI
    | EImult : ExprI -> ExprI -> ExprI
    | EImax : ExprI -> ExprI -> ExprI
    | EIraw : int -> ExprI.

  Inductive ExprZ : Set :=
    | EZplus : ExprZ -> ExprZ -> ExprZ
    | EZopp : ExprZ -> ExprZ
    | EZminus : ExprZ -> ExprZ -> ExprZ
    | EZmult : ExprZ -> ExprZ -> ExprZ
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
    match constr:trm with
      | 0 => constr:EI0
      | 1 => constr:EI1
      | 2 => constr:EI2
      | 3 => constr:EI3
      | ?x + ?y => let ex := i2ei x with ey := i2ei y in constr:(EIplus ex ey)
      | ?x - ?y => let ex := i2ei x with ey := i2ei y in constr:(EIminus ex ey)
      | ?x * ?y => let ex := i2ei x with ey := i2ei y in constr:(EImult ex ey)
      | max ?x ?y => let ex := i2ei x with ey := i2ei y in constr:(EImax ex ey)
      | - ?x => let ex := i2ei x in constr:(EIopp ex)
      | ?x => constr:(EIraw x)
    end

  (** [Z] to [ExprZ] *)

    with z2ez trm :=
    match constr:trm with
      | (?x+?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EZplus ex ey)
      | (?x-?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EZminus ex ey)
      | (?x*?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EZmult ex ey)
      | (Zmax ?x ?y) => let ex := z2ez x with ey := z2ez y in constr:(EZmax ex ey)
      | (-?x)%Z =>  let ex := z2ez x in constr:(EZopp ex)
      | i2z ?x => let ex := i2ei x in constr:(EZofI ex)
      | ?x => constr:(EZraw x)
    end.

  (** [Prop] to [ExprP] *)

  Ltac p2ep trm :=
    match constr:trm with
      | (?x <-> ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPequiv ex ey)
      | (?x -> ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPimpl ex ey)
      | (?x /\ ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPand ex ey)
      | (?x \/ ?y) => let ex := p2ep x with ey := p2ep y in constr:(EPor ex ey)
      | (~ ?x) => let ex := p2ep x in constr:(EPneg ex)
      | (eq (A:=Z) ?x ?y) => let ex := z2ez x with ey := z2ez y in constr:(EPeq ex ey)
      | (?x<?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPlt ex ey)
      | (?x<=?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPle ex ey)
      | (?x>?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPgt ex ey)
      | (?x>=?y)%Z => let ex := z2ez x with ey := z2ez y in constr:(EPge ex ey)
      | ?x =>  constr:(EPraw x)
    end.

  (** [ExprI] to [int] *)

  Fixpoint ei2i (e:ExprI) : int :=
    match e with
      | EI0 => 0
      | EI1 => 1
      | EI2 => 2
      | EI3 => 3
      | EIplus e1 e2 => (ei2i e1)+(ei2i e2)
      | EIminus e1 e2 => (ei2i e1)-(ei2i e2)
      | EImult e1 e2 => (ei2i e1)*(ei2i e2)
      | EImax e1 e2 => max (ei2i e1) (ei2i e2)
      | EIopp e => -(ei2i e)
      | EIraw i => i
    end.

  (** [ExprZ] to [Z] *)

  Fixpoint ez2z (e:ExprZ) : Z :=
    match e with
      | EZplus e1 e2 => ((ez2z e1)+(ez2z e2))%Z
      | EZminus e1 e2 => ((ez2z e1)-(ez2z e2))%Z
      | EZmult e1 e2 => ((ez2z e1)*(ez2z e2))%Z
      | EZmax e1 e2 => Zmax (ez2z e1) (ez2z e2)
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
      | EIplus e1 e2 => EZplus (norm_ei e1) (norm_ei e2)
      | EIminus e1 e2 => EZminus (norm_ei e1) (norm_ei e2)
      | EImult e1 e2 => EZmult (norm_ei e1) (norm_ei e2)
      | EImax e1 e2 => EZmax (norm_ei e1) (norm_ei e2)
      | EIopp e => EZopp (norm_ei e)
      | EIraw i => EZofI (EIraw i)
    end.

  (** [ExprZ] to a simplified [ExprZ] *)

  Fixpoint norm_ez (e:ExprZ) : ExprZ :=
    match e with
      | EZplus e1 e2 => EZplus (norm_ez e1) (norm_ez e2)
      | EZminus e1 e2 => EZminus (norm_ez e1) (norm_ez e2)
      | EZmult e1 e2 => EZmult (norm_ez e1) (norm_ez e2)
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

  Lemma norm_ei_correct : forall e:ExprI, ez2z (norm_ei e) = i2z (ei2i e).
  Proof.
    induction e; simpl; intros; i2z; auto; try congruence.
  Qed.

  Lemma norm_ez_correct : forall e:ExprZ, ez2z (norm_ez e) = ez2z e.
  Proof.
    induction e; simpl; intros; i2z; auto; try congruence; apply norm_ei_correct.
  Qed.

  Lemma norm_ep_correct :
    forall e:ExprP, ep2p (norm_ep e) <-> ep2p e.
  Proof.
    induction e; simpl; repeat (rewrite norm_ez_correct); intuition.
  Qed.

  Lemma norm_ep_correct2 :
    forall e:ExprP, ep2p (norm_ep e) -> ep2p e.
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
  Open Scope Z_scope.
  Definition int := Z.
  Definition _0 := 0.
  Definition _1 := 1.
  Definition _2 := 2.
  Definition _3 := 3.
  Definition plus := Zplus.
  Definition opp := Zopp.
  Definition minus := Zminus.
  Definition mult := Zmult.
  Definition max := Zmax.
  Definition gt_le_dec := Z_gt_le_dec.
  Definition ge_lt_dec := Z_ge_lt_dec.
  Definition eq_dec := Z_eq_dec.
  Definition i2z : int -> Z := fun n => n.
  Lemma i2z_eq : forall n p, i2z n=i2z p -> n = p. Proof. auto. Qed.
  Lemma i2z_0 : i2z _0 = 0.  Proof. auto. Qed.
  Lemma i2z_1 : i2z _1 = 1.  Proof. auto. Qed.
  Lemma i2z_2 : i2z _2 = 2.  Proof. auto. Qed.
  Lemma i2z_3 : i2z _3 = 3.  Proof. auto. Qed.
  Lemma i2z_plus : forall n p, i2z (n + p) = i2z n + i2z p.  Proof. auto. Qed.
  Lemma i2z_opp : forall n, i2z (- n)  = - i2z n.  Proof. auto. Qed.
  Lemma i2z_minus : forall n p, i2z (n - p)  = i2z n - i2z p.  Proof. auto. Qed.
  Lemma i2z_mult : forall n p, i2z (n * p)  = i2z n * i2z p.  Proof. auto. Qed.
  Lemma i2z_max : forall n p, i2z (max n p) = Zmax (i2z n) (i2z p). Proof. auto. Qed.
End Z_as_Int.

