(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The type [bool] is defined in the prelude as
    [Inductive bool : Set := true : bool | false : bool] *)

(** Most of the lemmas in this file are trivial after breaking all booleans *)

Ltac destr_bool :=
 intros; destruct_all bool; simpl in *; trivial; try discriminate.

(** Interpretation of booleans as propositions *)

Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

(*******************)
(** * Decidability *)
(*******************)

Lemma bool_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
Proof.
  decide equality.
Defined.

(*********************)
(** * Discrimination *)
(*********************)

Lemma diff_true_false : true <> false.
Proof.
  discriminate.
Qed.
Hint Resolve diff_true_false : bool.

Lemma diff_false_true : false <> true.
Proof.
  discriminate.
Qed.
Hint Resolve diff_false_true : bool.
Hint Extern 1 (false <> true) => exact diff_false_true.

Lemma eq_true_false_abs : forall b:bool, b = true -> b = false -> False.
Proof.
  destr_bool.
Qed.

Lemma not_true_is_false : forall b:bool, b <> true -> b = false.
Proof.
  destr_bool; intuition.
Qed.

Lemma not_false_is_true : forall b:bool, b <> false -> b = true.
Proof.
  destr_bool; intuition.
Qed.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof.
  destr_bool; intuition.
Qed.

Lemma not_false_iff_true : forall b, b <> false <-> b = true.
Proof.
  destr_bool; intuition.
Qed.

(**********************)
(** * Order on booleans *)
(**********************)

Definition leb (b1 b2:bool) :=
  match b1 with
    | true => b2 = true
    | false => True
  end.
Hint Unfold leb: bool.

Lemma leb_implb : forall b1 b2, leb b1 b2 <-> implb b1 b2 = true.
Proof.
  destr_bool; intuition.
Qed.

(* Infix "<=" := leb : bool_scope. *)

(*************)
(** * Equality *)
(*************)

Definition eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Lemma eqb_subst :
  forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
Proof.
  destr_bool.
Qed.

Lemma eqb_reflx : forall b:bool, eqb b b = true.
Proof.
  destr_bool.
Qed.

Lemma eqb_prop : forall a b:bool, eqb a b = true -> a = b.
Proof.
  destr_bool.
Qed.

Lemma eqb_true_iff : forall a b:bool, eqb a b = true <-> a = b.
Proof.
  destr_bool; intuition.
Qed.

Lemma eqb_false_iff : forall a b:bool, eqb a b = false <-> a <> b.
Proof.
  destr_bool; intuition.
Qed.

(************************)
(** * A synonym of [if] on [bool] *)
(************************)

Definition ifb (b1 b2 b3:bool) : bool :=
  match b1 with
    | true => b2
    | false => b3
  end.

Open Scope bool_scope.

(****************************)
(** * De Morgan laws          *)
(****************************)

Lemma negb_orb : forall b1 b2:bool, negb (b1 || b2) = negb b1 && negb b2.
Proof.
  destr_bool.
Qed.

Lemma negb_andb : forall b1 b2:bool, negb (b1 && b2) = negb b1 || negb b2.
Proof.
  destr_bool.
Qed.

(********************************)
(** * Properties of [negb]    *)
(********************************)

Lemma negb_involutive : forall b:bool, negb (negb b) = b.
Proof.
  destr_bool.
Qed.

Lemma negb_involutive_reverse : forall b:bool, b = negb (negb b).
Proof.
  destr_bool.
Qed.

Notation negb_elim := negb_involutive (only parsing).
Notation negb_intro := negb_involutive_reverse (only parsing).

Lemma negb_sym : forall b b':bool, b' = negb b -> b = negb b'.
Proof.
  destr_bool.
Qed.

Lemma no_fixpoint_negb : forall b:bool, negb b <> b.
Proof.
  destr_bool.
Qed.

Lemma eqb_negb1 : forall b:bool, eqb (negb b) b = false.
Proof.
  destr_bool.
Qed.

Lemma eqb_negb2 : forall b:bool, eqb b (negb b) = false.
Proof.
  destr_bool.
Qed.

Lemma if_negb :
  forall (A:Type) (b:bool) (x y:A),
    (if negb b then x else y) = (if b then y else x).
Proof.
  destr_bool.
Qed.

Lemma negb_true_iff : forall b, negb b = true <-> b = false.
Proof.
  destr_bool; intuition.
Qed.

Lemma negb_false_iff : forall b, negb b = false <-> b = true.
Proof.
  destr_bool; intuition.
Qed.


(********************************)
(** * Properties of [orb]     *)
(********************************)

Lemma orb_true_iff :
  forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  destr_bool; intuition.
Qed.

Lemma orb_false_iff :
  forall b1 b2, b1 || b2 = false <-> b1 = false /\ b2 = false.
Proof.
  destr_bool; intuition.
Qed.

Lemma orb_true_elim :
  forall b1 b2:bool, b1 || b2 = true -> {b1 = true} + {b2 = true}.
Proof.
  destruct b1; simpl; auto.
Defined.

Lemma orb_prop : forall a b:bool, a || b = true -> a = true \/ b = true.
Proof.
 intros; apply orb_true_iff; trivial.
Qed.

Lemma orb_true_intro :
  forall b1 b2:bool, b1 = true \/ b2 = true -> b1 || b2 = true.
Proof.
 intros; apply orb_true_iff; trivial.
Qed.
Hint Resolve orb_true_intro: bool.

Lemma orb_false_intro :
  forall b1 b2:bool, b1 = false -> b2 = false -> b1 || b2 = false.
Proof.
 intros. subst. reflexivity.
Qed.
Hint Resolve orb_false_intro: bool.

Lemma orb_false_elim :
  forall b1 b2:bool, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof.
  intros. apply orb_false_iff; trivial.
Qed.

Lemma orb_diag : forall b, b || b = b.
Proof.
 destr_bool.
Qed.

(** [true] is a zero for [orb] *)

Lemma orb_true_r : forall b:bool, b || true = true.
Proof.
  destr_bool.
Qed.
Hint Resolve orb_true_r: bool.

Lemma orb_true_l : forall b:bool, true || b = true.
Proof.
  reflexivity.
Qed.

Notation orb_b_true := orb_true_r (only parsing).
Notation orb_true_b := orb_true_l (only parsing).

(** [false] is neutral for [orb] *)

Lemma orb_false_r : forall b:bool, b || false = b.
Proof.
  destr_bool.
Qed.
Hint Resolve orb_false_r: bool.

Lemma orb_false_l : forall b:bool, false || b = b.
Proof.
  destr_bool.
Qed.
Hint Resolve orb_false_l: bool.

Notation orb_b_false := orb_false_r (only parsing).
Notation orb_false_b := orb_false_l (only parsing).

(** Complementation *)

Lemma orb_negb_r : forall b:bool, b || negb b = true.
Proof.
  destr_bool.
Qed.
Hint Resolve orb_negb_r: bool.

Notation orb_neg_b := orb_negb_r (only parsing).

(** Commutativity *)

Lemma orb_comm : forall b1 b2:bool, b1 || b2 = b2 || b1.
Proof.
  destr_bool.
Qed.

(** Associativity *)

Lemma orb_assoc : forall b1 b2 b3:bool, b1 || (b2 || b3) = b1 || b2 || b3.
Proof.
  destr_bool.
Qed.
Hint Resolve orb_comm orb_assoc: bool.

(*******************************)
(** * Properties of [andb]     *)
(*******************************)

Lemma andb_true_iff :
  forall b1 b2:bool, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  destr_bool; intuition.
Qed.

Lemma andb_false_iff :
  forall b1 b2:bool, b1 && b2 = false <-> b1 = false \/ b2 = false.
Proof.
  destr_bool; intuition.
Qed.

Lemma andb_true_eq :
  forall a b:bool, true = a && b -> true = a /\ true = b.
Proof.
  destr_bool. auto.
Defined.

Lemma andb_false_intro1 : forall b1 b2:bool, b1 = false -> b1 && b2 = false.
Proof.
  intros. apply andb_false_iff. auto.
Qed.

Lemma andb_false_intro2 : forall b1 b2:bool, b2 = false -> b1 && b2 = false.
Proof.
  intros. apply andb_false_iff. auto.
Qed.

(** [false] is a zero for [andb] *)

Lemma andb_false_r : forall b:bool, b && false = false.
Proof.
  destr_bool.
Qed.

Lemma andb_false_l : forall b:bool, false && b = false.
Proof.
  reflexivity.
Qed.

Notation andb_b_false := andb_false_r (only parsing).
Notation andb_false_b := andb_false_l (only parsing).

Lemma andb_diag : forall b, b && b = b.
Proof.
 destr_bool.
Qed.

(** [true] is neutral for [andb] *)

Lemma andb_true_r : forall b:bool, b && true = b.
Proof.
  destr_bool.
Qed.

Lemma andb_true_l : forall b:bool, true && b = b.
Proof.
  reflexivity.
Qed.

Notation andb_b_true := andb_true_r (only parsing).
Notation andb_true_b := andb_true_l (only parsing).

Lemma andb_false_elim :
  forall b1 b2:bool, b1 && b2 = false -> {b1 = false} + {b2 = false}.
Proof.
  destruct b1; simpl; auto.
Defined.
Hint Resolve andb_false_elim: bool.

(** Complementation *)

Lemma andb_negb_r : forall b:bool, b && negb b = false.
Proof.
  destr_bool.
Qed.
Hint Resolve andb_negb_r: bool.

Notation andb_neg_b := andb_negb_r (only parsing).

(** Commutativity *)

Lemma andb_comm : forall b1 b2:bool, b1 && b2 = b2 && b1.
Proof.
  destr_bool.
Qed.

(** Associativity *)

Lemma andb_assoc : forall b1 b2 b3:bool, b1 && (b2 && b3) = b1 && b2 && b3.
Proof.
  destr_bool.
Qed.

Hint Resolve andb_comm andb_assoc: bool.

(*******************************************)
(** * Properties mixing [andb] and [orb] *)
(*******************************************)

(** Distributivity *)

Lemma andb_orb_distrib_r :
  forall b1 b2 b3:bool, b1 && (b2 || b3) = b1 && b2 || b1 && b3.
Proof.
  destr_bool.
Qed.

Lemma andb_orb_distrib_l :
 forall b1 b2 b3:bool, (b1 || b2) && b3 = b1 && b3 || b2 && b3.
Proof.
  destr_bool.
Qed.

Lemma orb_andb_distrib_r :
  forall b1 b2 b3:bool, b1 || b2 && b3 = (b1 || b2) && (b1 || b3).
Proof.
  destr_bool.
Qed.

Lemma orb_andb_distrib_l :
  forall b1 b2 b3:bool, b1 && b2 || b3 = (b1 || b3) && (b2 || b3).
Proof.
  destr_bool.
Qed.

(* Compatibility *)
Notation demorgan1 := andb_orb_distrib_r (only parsing).
Notation demorgan2 := andb_orb_distrib_l (only parsing).
Notation demorgan3 := orb_andb_distrib_r (only parsing).
Notation demorgan4 := orb_andb_distrib_l (only parsing).

(** Absorption *)

Lemma absorption_andb : forall b1 b2:bool, b1 && (b1 || b2) = b1.
Proof.
  destr_bool.
Qed.

Lemma absorption_orb : forall b1 b2:bool, b1 || b1 && b2 = b1.
Proof.
  destr_bool.
Qed.

(* begin hide *)
(* Compatibility *)
Notation absoption_andb := absorption_andb (only parsing).
Notation absoption_orb := absorption_orb (only parsing).
(* end hide *)

(*********************************)
(** * Properties of [xorb]       *)
(*********************************)

(** [false] is neutral for [xorb] *)

Lemma xorb_false_r : forall b:bool, xorb b false = b.
Proof.
  destr_bool.
Qed.

Lemma xorb_false_l : forall b:bool, xorb false b = b.
Proof.
  destr_bool.
Qed.

Notation xorb_false := xorb_false_r (only parsing).
Notation false_xorb := xorb_false_l (only parsing).

(** [true] is "complementing" for [xorb] *)

Lemma xorb_true_r : forall b:bool, xorb b true = negb b.
Proof.
  reflexivity.
Qed.

Lemma xorb_true_l : forall b:bool, xorb true b = negb b.
Proof.
  reflexivity.
Qed.

Notation xorb_true := xorb_true_r (only parsing).
Notation true_xorb := xorb_true_l (only parsing).

(** Nilpotency (alternatively: identity is a inverse for [xorb]) *)

Lemma xorb_nilpotent : forall b:bool, xorb b b = false.
Proof.
  destr_bool.
Qed.

(** Commutativity *)

Lemma xorb_comm : forall b b':bool, xorb b b' = xorb b' b.
Proof.
  destr_bool.
Qed.

(** Associativity *)

Lemma xorb_assoc_reverse :
  forall b b' b'':bool, xorb (xorb b b') b'' = xorb b (xorb b' b'').
Proof.
  destr_bool.
Qed.

Notation xorb_assoc := xorb_assoc_reverse (only parsing). (* Compatibility *)

Lemma xorb_eq : forall b b':bool, xorb b b' = false -> b = b'.
Proof.
  destr_bool.
Qed.

Lemma xorb_move_l_r_1 :
  forall b b' b'':bool, xorb b b' = b'' -> b' = xorb b b''.
Proof.
  destr_bool.
Qed.

Lemma xorb_move_l_r_2 :
  forall b b' b'':bool, xorb b b' = b'' -> b = xorb b'' b'.
Proof.
  destr_bool.
Qed.

Lemma xorb_move_r_l_1 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b' b = b''.
Proof.
  destr_bool.
Qed.

Lemma xorb_move_r_l_2 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b b'' = b'.
Proof.
  destr_bool.
Qed.

Lemma negb_xorb_l : forall b b', negb (xorb b b') = xorb (negb b) b'.
Proof.
 destruct b,b'; trivial.
Qed.

Lemma negb_xorb_r : forall b b', negb (xorb b b') = xorb b (negb b').
Proof.
 destruct b,b'; trivial.
Qed.

Lemma xorb_negb_negb : forall b b', xorb (negb b) (negb b') = xorb b b'.
Proof.
 destruct b,b'; trivial.
Qed.

(** Lemmas about the [b = true] embedding of [bool] to [Prop] *)

Lemma eq_iff_eq_true : forall b1 b2, b1 = b2 <-> (b1 = true <-> b2 = true).
Proof.
  destr_bool; intuition.
Qed.

Lemma eq_true_iff_eq : forall b1 b2, (b1 = true <-> b2 = true) -> b1 = b2.
Proof.
  apply eq_iff_eq_true.
Qed.

Notation bool_1 := eq_true_iff_eq (only parsing). (* Compatibility *)

Lemma eq_true_negb_classical : forall b:bool, negb b <> true -> b = true.
Proof.
  destr_bool; intuition.
Qed.

Notation bool_3 := eq_true_negb_classical (only parsing). (* Compatibility *)

Lemma eq_true_not_negb : forall b:bool, b <> true -> negb b = true.
Proof.
  destr_bool; intuition.
Qed.

Notation bool_6 := eq_true_not_negb (only parsing). (* Compatibility *)

Hint Resolve eq_true_not_negb : bool.

(* An interesting lemma for auto but too strong to keep compatibility *)

Lemma absurd_eq_bool : forall b b':bool, False -> b = b'.
Proof.
  contradiction.
Qed.

(* A more specific one that preserves compatibility with old hint bool_3 *)

Lemma absurd_eq_true : forall b, False -> b = true.
Proof.
  contradiction.
Qed.
Hint Resolve absurd_eq_true.

(* A specific instance of eq_trans that preserves compatibility with
   old hint bool_2 *)

Lemma trans_eq_bool : forall x y z:bool, x = y -> y = z -> x = z.
Proof.
  apply eq_trans.
Qed.
Hint Resolve trans_eq_bool.

(*****************************************)
(** * Reflection of [bool] into [Prop] *)
(*****************************************)

(** [Is_true] and equality *)

Hint Unfold Is_true: bool.

Lemma Is_true_eq_true : forall x:bool, Is_true x -> x = true.
Proof.
  destr_bool; tauto.
Qed.

Lemma Is_true_eq_left : forall x:bool, x = true -> Is_true x.
Proof.
  intros; subst; auto with bool.
Qed.

Lemma Is_true_eq_right : forall x:bool, true = x -> Is_true x.
Proof.
  intros; subst; auto with bool.
Qed.

Notation Is_true_eq_true2 := Is_true_eq_right (only parsing).

Hint Immediate Is_true_eq_right Is_true_eq_left: bool.

Lemma eqb_refl : forall x:bool, Is_true (eqb x x).
Proof.
  destr_bool.
Qed.

Lemma eqb_eq : forall x y:bool, Is_true (eqb x y) -> x = y.
Proof.
  destr_bool; tauto.
Qed.

(** [Is_true] and connectives *)

Lemma orb_prop_elim :
  forall a b:bool, Is_true (a || b) -> Is_true a \/ Is_true b.
Proof.
  destr_bool; tauto.
Qed.

Notation orb_prop2 := orb_prop_elim (only parsing).

Lemma orb_prop_intro :
  forall a b:bool, Is_true a \/ Is_true b -> Is_true (a || b).
Proof.
  destr_bool; tauto.
Qed.

Lemma andb_prop_intro :
  forall b1 b2:bool, Is_true b1 /\ Is_true b2 -> Is_true (b1 && b2).
Proof.
  destr_bool; tauto.
Qed.
Hint Resolve andb_prop_intro: bool.

Notation andb_true_intro2 :=
  (fun b1 b2 H1 H2 => andb_prop_intro b1 b2 (conj H1 H2))
  (only parsing).

Lemma andb_prop_elim :
  forall a b:bool, Is_true (a && b) -> Is_true a /\ Is_true b.
Proof.
  destr_bool; auto.
Qed.
Hint Resolve andb_prop_elim: bool.

Notation andb_prop2 := andb_prop_elim (only parsing).

Lemma eq_bool_prop_intro :
  forall b1 b2, (Is_true b1 <-> Is_true b2) -> b1 = b2.
Proof.
  destr_bool; tauto.
Qed.

Lemma eq_bool_prop_elim : forall b1 b2, b1 = b2 -> (Is_true b1 <-> Is_true b2).
Proof.
  destr_bool; tauto.
Qed.

Lemma negb_prop_elim : forall b, Is_true (negb b) -> ~ Is_true b.
Proof.
  destr_bool; tauto.
Qed.

Lemma negb_prop_intro : forall b, ~ Is_true b -> Is_true (negb b).
Proof.
  destr_bool; tauto.
Qed.

Lemma negb_prop_classical : forall b, ~ Is_true (negb b) -> Is_true b.
Proof.
  destr_bool; tauto.
Qed.

Lemma negb_prop_involutive : forall b, Is_true b -> ~ Is_true (negb b).
Proof.
  destr_bool; tauto.
Qed.

(** Rewrite rules about andb, orb and if (used in romega) *)

Lemma andb_if : forall (A:Type)(a a':A)(b b' : bool),
  (if b && b' then a else a') =
  (if b then if b' then a else a' else a').
Proof.
  destr_bool.
Qed.

Lemma negb_if : forall (A:Type)(a a':A)(b:bool),
 (if negb b then a else a') =
 (if b then a' else a).
Proof.
  destr_bool.
Qed.

(*****************************************)
(** * Alternative versions of [andb] and [orb]
    with lazy behavior (for vm_compute)  *)
(*****************************************)

Notation "a &&& b" := (if a then b else false)
 (at level 40, left associativity) : lazy_bool_scope.
Notation "a ||| b" := (if a then true else b)
 (at level 50, left associativity) : lazy_bool_scope.

Local Open Scope lazy_bool_scope.

Lemma andb_lazy_alt : forall a b : bool, a && b = a &&& b.
Proof.
  reflexivity.
Qed.

Lemma orb_lazy_alt : forall a b : bool, a || b = a ||| b.
Proof.
  reflexivity.
Qed.

(*****************************************)
(** * Reflect: a specialized inductive type for
    relating propositions and booleans,
    as popularized by the Ssreflect library. *)
(*****************************************)

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.
Hint Constructors reflect : bool.

(** Interest: a case on a reflect lemma or hyp performs clever
    unification, and leave the goal in a convenient shape
    (a bit like case_eq). *)

(** Relation with iff : *)

Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
Proof.
 destruct 1; intuition; discriminate.
Qed.

Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
Proof.
 destr_bool; intuition.
Defined.

(** It would be nice to join [reflect_iff] and [iff_reflect]
    in a unique [iff] statement, but this isn't allowed since
    [iff] is in Prop. *)

(** Reflect implies decidability of the proposition *)

Lemma reflect_dec : forall P b, reflect P b -> {P}+{~P}.
Proof.
 destruct 1; auto.
Defined.

(** Reciprocally, from a decidability, we could state a
    [reflect] as soon as we have a [bool_of_sumbool]. *)

(** For instance, we could state the correctness of [Bool.eqb] via [reflect]: *)

Lemma eqb_spec (b b' : bool) : reflect (b = b') (eqb b b').
Proof.
 destruct b, b'; now constructor.
Qed.
