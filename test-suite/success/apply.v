(* Test apply in *)

Goal (forall x y, x = S y -> y=y) -> 2 = 4 -> 3=3.
intros H H0.
apply H in H0.
assumption.
Qed.

Require Import ZArith.
Open Scope Z_scope.
Goal forall x y z, ~ z <= 0 -> x * z < y * z -> x <= y.
intros; apply Znot_le_gt, Zgt_lt in H.
apply Zmult_lt_reg_r, Zlt_le_weak in H0; auto.
Qed.

(* Check if it unfolds when there are not enough premises *)

Goal forall n, n = S n -> False.
intros.
apply n_Sn in H.
assumption.
Qed.

(* Check naming in with bindings; printing used to be inconsistent before *)
(* revision 9450 *)

Notation S':=S (only parsing).
Goal (forall S, S = S' S) -> (forall S, S = S' S).
intros.
apply H with (S0 := S).

(* Check inference of implicit arguments in bindings *)

Goal exists y : nat -> Type, y 0 = y 0.
exists (fun x => True).
trivial.
Qed.

(* Check universe handling in typed unificationn *)

Definition E := Type.
Goal exists y : E, y = y.
exists Prop.
trivial.
Qed.

Definition E := Type.
Variable Eq : Prop = (Prop -> Prop) :> E.
Goal Prop.
rewrite Eq.
Abort.

(* Check insertion of coercions in bindings *)

Coercion eq_true : bool >-> Sortclass.
Goal exists A:Prop, A = A.
exists true.
trivial.
Qed.

(* Check use of unification of bindings types in specialize *)

Variable P : nat -> Prop.
Variable L : forall (l : nat), P l -> P l.
Goal P 0 -> True.
intros.
specialize L with (1:=H).
Abort.
Reset P.

(* Two examples that show that hnf_constr is used when unifying types
   of bindings *)

Require Import List.
Open Scope list_scope.
Fixpoint P (l : list nat) : Prop :=
  match l with
  | nil => True
  | e1 :: nil => e1 = e1
  | e1 :: l1 => e1 = e1 /\ P l1
  end.
Variable L : forall n l, P (n::l) -> P l.

Goal forall (x:nat) l, P (x::l) -> P l.
intros.
apply L with (1:=H).
Qed.

Goal forall (x:nat) l, match l with nil => x=x | _::_ => x=x /\ P l end -> P l.
intros.
apply L with (1:=H).
Qed.



