(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** The type [bool] is defined in the prelude as
    [Inductive bool : Set := true : bool | false : bool] *)

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
  unfold not in |- *; intro contr; change (Is_true false) in |- *.
  elim contr; simpl in |- *; trivial.
Qed.
Hint Resolve diff_true_false : bool v62.

Lemma diff_false_true : false <> true.
Proof. 
  red in |- *; intros H; apply diff_true_false.
  symmetry  in |- *.
assumption.
Qed.
Hint Resolve diff_false_true : bool v62.
Hint Extern 1 (false <> true) => exact diff_false_true.

Lemma eq_true_false_abs : forall b:bool, b = true -> b = false -> False.
Proof.
  intros b H; rewrite H; auto with bool.
Qed.

Lemma not_true_is_false : forall b:bool, b <> true -> b = false.
Proof.
  destruct b.
  intros.
  red in H; elim H.
  reflexivity.
  intros abs.
  reflexivity.
Qed.

Lemma not_false_is_true : forall b:bool, b <> false -> b = true.
Proof.
  destruct b.
  intros.
  reflexivity.
  intro H; red in H; elim H.
  reflexivity.
Qed.

(**********************)
(** * Order on booleans *)
(**********************)

Definition leb (b1 b2:bool) :=
  match b1 with
    | true => b2 = true
    | false => True
  end.
Hint Unfold leb: bool v62.

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
  unfold eqb in |- *.
  intros P b1.
  intros b2.
  case b1.
  case b2.
  trivial with bool.
  intros H.
  inversion_clear H.
  case b2.
  intros H.
  inversion_clear H.
  trivial with bool.
Qed.

Lemma eqb_reflx : forall b:bool, eqb b b = true.
Proof.
  intro b.
  case b.
  trivial with bool.
  trivial with bool.
Qed.

Lemma eqb_prop : forall a b:bool, eqb a b = true -> a = b.
Proof.
  destruct a; destruct b; simpl in |- *; intro; discriminate H || reflexivity.
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
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.

Lemma negb_andb : forall b1 b2:bool, negb (b1 && b2) = negb b1 || negb b2.
Proof.
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.

(********************************)
(** * Properties of [negb]    *)
(********************************)

Lemma negb_involutive : forall b:bool, negb (negb b) = b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma negb_involutive_reverse : forall b:bool, b = negb (negb b).
Proof.
  destruct b; reflexivity.
Qed.

Notation negb_elim := negb_involutive (only parsing).
Notation negb_intro := negb_involutive_reverse (only parsing).

Lemma negb_sym : forall b b':bool, b' = negb b -> b = negb b'.
Proof.
  destruct b; destruct b'; intros; simpl in |- *; trivial with bool.
Qed.

Lemma no_fixpoint_negb : forall b:bool, negb b <> b.
Proof.
  destruct b; simpl in |- *; intro; apply diff_true_false;
    auto with bool.
Qed.

Lemma eqb_negb1 : forall b:bool, eqb (negb b) b = false.
Proof.
  destruct b.
  trivial with bool.
  trivial with bool.
Qed.
 
Lemma eqb_negb2 : forall b:bool, eqb b (negb b) = false.
Proof.
  destruct b.
  trivial with bool.
  trivial with bool.
Qed.


Lemma if_negb :
  forall (A:Set) (b:bool) (x y:A),
    (if negb b then x else y) = (if b then y else x).
Proof.
  destruct b; trivial.
Qed.


(********************************)
(** * Properties of [orb]     *)
(********************************)

Lemma orb_true_elim :
  forall b1 b2:bool, b1 || b2 = true -> {b1 = true} + {b2 = true}.
Proof.
  destruct b1; simpl in |- *; auto with bool.
Defined.

Lemma orb_prop : forall a b:bool, a || b = true -> a = true \/ b = true.
Proof.
  destruct a; destruct b; simpl in |- *; try (intro H; discriminate H);
    auto with bool.
Qed.

Lemma orb_true_intro :
  forall b1 b2:bool, b1 = true \/ b2 = true -> b1 || b2 = true.
Proof.
  destruct b1; auto with bool.
  destruct 1; intros.
  elim diff_true_false; auto with bool.
  rewrite H; trivial with bool.
Qed.
Hint Resolve orb_true_intro: bool v62.

Lemma orb_false_intro :
  forall b1 b2:bool, b1 = false -> b2 = false -> b1 || b2 = false.
Proof.
  intros b1 b2 H1 H2; rewrite H1; rewrite H2; trivial with bool.
Qed.
Hint Resolve orb_false_intro: bool v62.

(** [true] is a zero for [orb] *)

Lemma orb_true_r : forall b:bool, b || true = true.
Proof.
  auto with bool.
Qed.
Hint Resolve orb_true_r: bool v62.

Lemma orb_true_l : forall b:bool, true || b = true.
Proof.
  trivial with bool.
Qed.

Notation orb_b_true := orb_true_r (only parsing).
Notation orb_true_b := orb_true_l (only parsing).

(** [false] is neutral for [orb] *)

Lemma orb_false_r : forall b:bool, b || false = b.
Proof.
  destruct b; trivial with bool.
Qed.
Hint Resolve orb_false_r: bool v62.

Lemma orb_false_l : forall b:bool, false || b = b.
Proof.
  destruct b; trivial with bool.
Qed.
Hint Resolve orb_false_l: bool v62.

Notation orb_b_false := orb_false_r (only parsing).
Notation orb_false_b := orb_false_l (only parsing).

Lemma orb_false_elim :
  forall b1 b2:bool, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof.
  destruct b1.
  intros; elim diff_true_false; auto with bool.
  destruct b2.
  intros; elim diff_true_false; auto with bool.
  auto with bool.
Qed.

(** Complementation *)

Lemma orb_negb_r : forall b:bool, b || negb b = true.
Proof.
  destruct b; reflexivity.
Qed.
Hint Resolve orb_negb_r: bool v62.

Notation orb_neg_b := orb_negb_r (only parsing).

(** Commutativity *)

Lemma orb_comm : forall b1 b2:bool, b1 || b2 = b2 || b1.
Proof.
  destruct b1; destruct b2; reflexivity.
Qed.

(** Associativity *)

Lemma orb_assoc : forall b1 b2 b3:bool, b1 || (b2 || b3) = b1 || b2 || b3.
Proof.
  destruct b1; destruct b2; destruct b3; reflexivity.
Qed.
Hint Resolve orb_comm orb_assoc: bool v62.

(*******************************)
(** * Properties of [andb]     *)
(*******************************)

Lemma andb_true_iff : 
  forall b1 b2:bool, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
 destruct b1; destruct b2; intuition.
Qed.

Lemma andb_true_eq :
  forall a b:bool, true = a && b -> true = a /\ true = b.
Proof.
  destruct a; destruct b; auto.
Defined.

Lemma andb_false_intro1 : forall b1 b2:bool, b1 = false -> b1 && b2 = false.
Proof.
  destruct b1; destruct b2; simpl in |- *; tauto || auto with bool.
Qed.

Lemma andb_false_intro2 : forall b1 b2:bool, b2 = false -> b1 && b2 = false.
Proof.
  destruct b1; destruct b2; simpl in |- *; tauto || auto with bool.
Qed.

(** [false] is a zero for [andb] *)

Lemma andb_false_r : forall b:bool, b && false = false.
Proof.
  destruct b; auto with bool.
Qed.

Lemma andb_false_l : forall b:bool, false && b = false.
Proof.
  trivial with bool.
Qed.

Notation andb_b_false := andb_false_r (only parsing).
Notation andb_false_b := andb_false_l (only parsing).

(** [true] is neutral for [andb] *)

Lemma andb_true_r : forall b:bool, b && true = b.
Proof.
  destruct b; auto with bool.
Qed.

Lemma andb_true_l : forall b:bool, true && b = b.
Proof.
  trivial with bool.
Qed.

Notation andb_b_true := andb_true_r (only parsing).
Notation andb_true_b := andb_true_l (only parsing).

Lemma andb_false_elim :
  forall b1 b2:bool, b1 && b2 = false -> {b1 = false} + {b2 = false}.
Proof.
  destruct b1; simpl in |- *; auto with bool.
Defined.
Hint Resolve andb_false_elim: bool v62.

(** Complementation *)

Lemma andb_negb_r : forall b:bool, b && negb b = false.
Proof.
  destruct b; reflexivity.
Qed.   
Hint Resolve andb_negb_r: bool v62.

Notation andb_neg_b := andb_negb_r (only parsing).

(** Commutativity *)

Lemma andb_comm : forall b1 b2:bool, b1 && b2 = b2 && b1.
Proof.
  destruct b1; destruct b2; reflexivity.
Qed.

(** Associativity *)

Lemma andb_assoc : forall b1 b2 b3:bool, b1 && (b2 && b3) = b1 && b2 && b3.
Proof.
  destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Hint Resolve andb_comm andb_assoc: bool v62.

(*******************************************)
(** * Properties mixing [andb] and [orb] *)
(*******************************************)

(** Distributivity *)

Lemma andb_orb_distrib_r :
  forall b1 b2 b3:bool, b1 && (b2 || b3) = b1 && b2 || b1 && b3.
Proof.
  destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Lemma andb_orb_distrib_l :
 forall b1 b2 b3:bool, (b1 || b2) && b3 = b1 && b3 || b2 && b3.
Proof.
  destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Lemma orb_andb_distrib_r :
  forall b1 b2 b3:bool, b1 || b2 && b3 = (b1 || b2) && (b1 || b3).
Proof.
  destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Lemma orb_andb_distrib_l :
  forall b1 b2 b3:bool, b1 && b2 || b3 = (b1 || b3) && (b2 || b3).
Proof.
  destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

(* Compatibility *)
Notation demorgan1 := andb_orb_distrib_r (only parsing).
Notation demorgan2 := andb_orb_distrib_l (only parsing).
Notation demorgan3 := orb_andb_distrib_r (only parsing).
Notation demorgan4 := orb_andb_distrib_l (only parsing).

(** Absorption *)

Lemma absoption_andb : forall b1 b2:bool, b1 && (b1 || b2) = b1.
Proof.
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.

Lemma absoption_orb : forall b1 b2:bool, b1 || b1 && b2 = b1.
Proof.
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.

(*********************************)
(** * Properties of [xorb]       *)
(*********************************)

(** [false] is neutral for [xorb] *)

Lemma xorb_false_r : forall b:bool, xorb b false = b.
Proof.
  destruct b; trivial.
Qed.

Lemma xorb_false_l : forall b:bool, xorb false b = b.
Proof.
  destruct b; trivial.
Qed.

Notation xorb_false := xorb_false_r (only parsing).
Notation false_xorb := xorb_false_l (only parsing).

(** [true] is "complementing" for [xorb] *)

Lemma xorb_true_r : forall b:bool, xorb b true = negb b.
Proof.
  trivial.
Qed.

Lemma xorb_true_l : forall b:bool, xorb true b = negb b.
Proof.
  destruct b; trivial.
Qed.

Notation xorb_true := xorb_true_r (only parsing).
Notation true_xorb := xorb_true_l (only parsing).

(** Nilpotency (alternatively: identity is a inverse for [xorb]) *)

Lemma xorb_nilpotent : forall b:bool, xorb b b = false.
Proof.
  destruct b; trivial.
Qed.

(** Commutativity *)

Lemma xorb_comm : forall b b':bool, xorb b b' = xorb b' b.
Proof.
  destruct b; destruct b'; trivial.
Qed.

(** Associativity *)

Lemma xorb_assoc_reverse :
  forall b b' b'':bool, xorb (xorb b b') b'' = xorb b (xorb b' b'').
Proof.
  destruct b; destruct b'; destruct b''; trivial.
Qed.

Notation xorb_assoc := xorb_assoc_reverse (only parsing). (* Compatibility *)

Lemma xorb_eq : forall b b':bool, xorb b b' = false -> b = b'.
Proof.
  destruct b; destruct b'; trivial.
  unfold xorb in |- *. intros. rewrite H. reflexivity.
Qed.

Lemma xorb_move_l_r_1 :
  forall b b' b'':bool, xorb b b' = b'' -> b' = xorb b b''.
Proof.
  intros. rewrite <- (false_xorb b'). rewrite <- (xorb_nilpotent b). rewrite xorb_assoc.
  rewrite H. reflexivity.
Qed.

Lemma xorb_move_l_r_2 :
  forall b b' b'':bool, xorb b b' = b'' -> b = xorb b'' b'.
Proof.
  intros. rewrite xorb_comm in H. rewrite (xorb_move_l_r_1 b' b b'' H). apply xorb_comm.
Qed.

Lemma xorb_move_r_l_1 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b' b = b''.
Proof.
  intros. rewrite H. rewrite <- xorb_assoc. rewrite xorb_nilpotent. apply false_xorb.
Qed.

Lemma xorb_move_r_l_2 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b b'' = b'.
Proof.
  intros. rewrite H. rewrite xorb_assoc. rewrite xorb_nilpotent. apply xorb_false.
Qed.

(** Lemmas about the [b = true] embedding of [bool] to [Prop] *)

Lemma eq_true_iff_eq : forall b1 b2, (b1 = true <-> b2 = true) -> b1 = b2. 
Proof. 
  intros b1 b2; case b1; case b2; intuition.
Qed.

Notation bool_1 := eq_true_iff_eq (only parsing). (* Compatibility *)

Lemma eq_true_negb_classical : forall b:bool, negb b <> true -> b = true.
Proof.
  destruct b; intuition.
Qed.

Notation bool_3 := eq_true_negb_classical (only parsing). (* Compatibility *)

Lemma eq_true_not_negb : forall b:bool, b <> true -> negb b = true.  
Proof.
  destruct b; intuition.
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

(* A specific instance of trans_eq that preserves compatibility with
   old hint bool_2 *)

Lemma trans_eq_bool : forall x y z:bool, x = y -> y = z -> x = z.
Proof.
  apply trans_eq.
Qed.
Hint Resolve trans_eq_bool.

(*****************************************)
(** * Reflection of [bool] into [Prop] *)
(*****************************************)

(** [Is_true] and equality *)

Hint Unfold Is_true: bool.

Lemma Is_true_eq_true : forall x:bool, Is_true x -> x = true.
Proof.
  destruct x; simpl in |- *; tauto.
Qed.

Lemma Is_true_eq_left : forall x:bool, x = true -> Is_true x.
Proof.
  intros; rewrite H; auto with bool.
Qed.

Lemma Is_true_eq_right : forall x:bool, true = x -> Is_true x.
Proof.
  intros; rewrite <- H; auto with bool.
Qed.

Notation Is_true_eq_true2 := Is_true_eq_right (only parsing).

Hint Immediate Is_true_eq_right Is_true_eq_left: bool.

Lemma eqb_refl : forall x:bool, Is_true (eqb x x).
Proof.
  destruct x; simpl; auto with bool.
Qed.

Lemma eqb_eq : forall x y:bool, Is_true (eqb x y) -> x = y.
Proof.
  destruct x; destruct y; simpl; tauto.
Qed.

(** [Is_true] and connectives *)

Lemma orb_prop_elim : 
  forall a b:bool, Is_true (a || b) -> Is_true a \/ Is_true b.
Proof.
  destruct a; destruct b; simpl; tauto.
Qed.

Notation orb_prop2 := orb_prop_elim (only parsing).

Lemma orb_prop_intro : 
  forall a b:bool, Is_true a \/ Is_true b -> Is_true (a || b).
Proof.
  destruct a; destruct b; simpl; tauto.
Qed.

Lemma andb_prop_intro :
  forall b1 b2:bool, Is_true b1 /\ Is_true b2 -> Is_true (b1 && b2).
Proof.
  destruct b1; destruct b2; simpl in |- *; tauto.
Qed.
Hint Resolve andb_prop_intro: bool v62.

Notation andb_true_intro2 :=
  (fun b1 b2 H1 H2 => andb_prop_intro b1 b2 (conj H1 H2))
  (only parsing).

Lemma andb_prop_elim :
  forall a b:bool, Is_true (a && b) -> Is_true a /\ Is_true b.
Proof.
  destruct a; destruct b; simpl in |- *; try (intro H; discriminate H);
    auto with bool.
Qed.
Hint Resolve andb_prop_elim: bool v62.

Notation andb_prop2 := andb_prop_elim (only parsing).

Lemma eq_bool_prop_intro : 
  forall b1 b2, (Is_true b1 <-> Is_true b2) -> b1 = b2. 
Proof. 
  destruct b1; destruct b2; simpl in *; intuition.
Qed.

Lemma eq_bool_prop_elim : forall b1 b2, b1 = b2 -> (Is_true b1 <-> Is_true b2).
Proof. 
  intros b1 b2; case b1; case b2; intuition.
Qed. 

Lemma negb_prop_elim : forall b, Is_true (negb b) -> ~ Is_true b.
Proof.
  destruct b; intuition.
Qed.

Lemma negb_prop_intro : forall b, ~ Is_true b -> Is_true (negb b).
Proof.
  destruct b; simpl in *; intuition.
Qed.

Lemma negb_prop_classical : forall b, ~ Is_true (negb b) -> Is_true b.
Proof.
  destruct b; intuition.
Qed.

Lemma negb_prop_involutive : forall b, Is_true b -> ~ Is_true (negb b).
Proof.
  destruct b; intuition.
Qed.

(* Rewrite rules about andb, orb and if (used in romega) *)

Lemma andb_if : forall (A:Set)(a a':A)(b b' : bool), 
  (if b && b' then a else a') = 
  (if b then if b' then a else a' else a').
Proof.
 destruct b; destruct b'; auto.
Qed.

Lemma negb_if : forall (A:Set)(a a':A)(b:bool), 
 (if negb b then a else a') = 
 (if b then a' else a).
Proof.
 destruct b; auto.
Qed.

(* Compatibility *)

Notation andb := Datatypes.andb (only parsing).
Notation orb := Datatypes.orb (only parsing).
Notation implb := Datatypes.implb (only parsing).
Notation xorb := Datatypes.xorb (only parsing).
Notation negb := Datatypes.negb (only parsing).
