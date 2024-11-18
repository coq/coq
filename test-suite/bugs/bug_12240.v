Require Import Setoid CMorphisms.

Set Implicit Arguments.

Inductive R A : A -> A -> Type :=
   (* with A -> A -> Prop here and Morphisms on top: no failure *)
   (* with relation A here and Morphisms on top: no failure *)
   (* with crelation A here and CMorphisms on top: no failure *)
| cR1 l : R l l
| cR2 l : R l l.  (* with only one constructor, only Fail 1 fails *)
#[export] Hint Constructors R : core.

#[export] Instance R_refl A : Reflexive (@R A).
Proof. auto. Qed.
#[export] Instance R_trans A : Transitive (@R A).
Proof. intros x y z HR1 HR2; destruct HR1, HR2; auto. Qed.

Goal forall (a b : nat), R a b -> R (id a) (id b).
Proof. intros a b H.
  (** This still fails but should be fixed when #7675 is. *)
  rewrite H; reflexivity. (* does not fail with nat inlined in the definition of R *)
    (* Fail 1 *)
    (* Tactic failure: setoid rewrite failed: ... *)
Qed.

Goal forall A (a b : A), R a b -> R (id a) (id b).
Proof. intros A a b H.
  rewrite H; reflexivity.
Abort.

Definition GuR A (uu : unit) := match uu with unit => @R A end.

#[export] Instance GuR_refl A uu : Reflexive (@GuR A uu).
Proof. destruct uu; apply R_refl. Qed.
#[export] Instance GuR_trans A uu : Transitive (@GuR A uu).
Proof. destruct uu; apply R_trans. Qed.

Goal forall uu (a b : nat), GuR uu a b -> GuR uu (id a) (id b).
Proof. intros uu a b H.
  rewrite H; reflexivity.
Abort.

Goal forall A uu (a b : A), GuR uu a b -> GuR uu (id a) (id b).
Proof. intros A uu a b H.
  rewrite H; reflexivity.
Abort.

Definition GbR A (bb : bool) := if bb then @R A else @R A.

#[export] Instance GbR_refl A bb : Reflexive (@GbR A bb).
Proof. destruct bb; apply R_refl. Qed.
#[export] Instance GbR_trans A bb : Transitive (@GbR A bb).
Proof. destruct bb; apply R_trans. Qed.

Goal forall bb (a b : nat), GbR bb a b -> GbR bb (id a) (id b).
Proof. intros bb a b H.
  rewrite H; reflexivity.
Qed.

Goal forall A bb (a b : A), GbR bb a b -> GbR bb (id a) (id b).
Proof. intros A bb a b H.
  rewrite H; reflexivity.
Qed.
