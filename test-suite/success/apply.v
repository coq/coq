(* Test apply in *)

Goal (forall x y, x = S y -> y=y) -> 2 = 4 -> 3=3.
intros H H0.
apply H in H0.
assumption.
Qed.

Require Import ZArith.
Goal (forall x y z, ~ z <= 0 -> x * z < y * z -> x <= y)%Z.
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
Qed.

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
   of bindings (a simplification of a script from Field_Theory) *)

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

(* The following call to auto fails if the type of the clause
   associated to the H is not beta-reduced [but apply H works]
   (a simplification of a script from FSetAVL) *)

Definition apply (f:nat->Prop) := forall x, f x.
Goal apply (fun n => n=0) -> 1=0.
intro H.
auto. 
Qed.

(* The following fails if the coercion Zpos is not introduced around p
   before trying a subterm that matches the left-hand-side of the equality
   (a simplication of an example taken from Nijmegen/QArith) *)

Require Import ZArith.
Coercion Zpos : positive >-> Z.
Variable f : Z -> Z -> Z.
Variable g : forall q1 q2 p : Z, f (f q1 p) (f q2 p) = Z0.
Goal forall p q1 q2, f (f q1 (Zpos p)) (f q2 (Zpos p)) = Z0.
intros; rewrite g with (p:=p).
reflexivity.
Qed.

(* A funny example where the behavior differs depending on which of a
   multiple solution to a unification problem is chosen (an instance
   of this case can be found in the proof of Buchberger.BuchRed.nf_divp) *)

Definition succ x := S x.
Goal forall (I : nat -> Set) (P : nat -> Prop) (Q : forall n:nat, I n -> Prop),
  (forall x y, P x -> Q x y) -> 
  (forall x, P (S x)) -> forall y: I (S 0), Q (succ 0) y.
intros.
apply H with (y:=y). 
(* [x] had two possible instances: [S 0], coming from unifying the
   type of [y] with [I ?n] and [succ 0] coming from the unification with
   the goal; only the first one allows to make the next apply (which
   does not work modulo delta) working *)
apply H0.
Qed.

(* A similar example with a arbitrary long conversion between the two
   possible instances *)

Fixpoint compute_succ x := 
  match x with O => S 0 | S n => S (compute_succ n) end.

Goal forall (I : nat -> Set) (P : nat -> Prop) (Q : forall n:nat, I n -> Prop),
  (forall x y, P x -> Q x y) -> 
  (forall x, P (S x)) -> forall y: I (S 100), Q (compute_succ 100) y.
intros.
apply H with (y:=y). 
apply H0.
Qed.

(* Another example with multiple convertible solutions to the same
   metavariable (extracted from Algebra.Hom_module.Hom_module, 10th
   subgoal which precisely fails) *)

Definition ID (A:Type) := A.
Goal forall f:Type -> Type, 
  forall (P : forall A:Type, A -> Prop), 
  (forall (B:Type) x, P (f B) x -> P (f B) x) -> 
  (forall (A:Type) x, P (f (f A)) x) -> 
  forall (A:Type) (x:f (f A)), P (f (ID (f A))) x.
intros.
apply H.
(* The parameter [B] had two possible instances: [ID (f A)] by direct
   unification and [f A] by unification of the type of [x]; only the
   first choice makes the next command fail, as it was
   (unfortunately?) in Hom_module *)
try apply H.
unfold ID; apply H0.
Qed.

(* Test coercion below product and on non meta-free terms in with bindings *)
(* Cf wishes #1408 from E. Makarov *)

Parameter bool_Prop :> bool -> Prop.
Parameter r : bool -> bool -> bool.
Axiom ax : forall (A : Set) (R : A -> A -> Prop) (x y : A), R x y.

Theorem t : r true false.
apply ax with (R := r).
Qed.
