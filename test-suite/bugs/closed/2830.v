(* Bug report #2830 (evar defined twice) covers different bugs *)

(* This was submitted by Anthony Crowley *)

Module A.

Set Implicit Arguments.

Inductive Bit := O | I.

Inductive BitString: nat -> Set :=
| bit: Bit -> BitString 0
| bitStr: forall n: nat, Bit -> BitString n -> BitString (S n).

Definition BitOr (a b: Bit) :=
  match a, b with
  | O, O => O
  | _, _ => I
  end.

(* Should fail with an error; used to failed in 8.4 and trunk with
   anomaly Evd.define: cannot define an evar twice *)

Fail Fixpoint StringOr (n m: nat) (a: BitString n) (b: BitString m) :=
  match a with
  | bit a' =>
      match b with
      | bit b' => bit (BitOr a' b')
      | bitStr b' bT => bitStr b' (StringOr (bit a') bT)
      end
  | bitStr a' aT =>
      match b with
      | bit b' => bitStr a' (StringOr aT (bit b'))
      | bitStr b' bT => bitStr (BitOr a' b') (StringOr aT bT)
      end
  end.

End A.

(* This was submitted by Andrew Appel *)

Module B.

Require Import Program Relations.

Record ageable_facts (A:Type) (level: A -> nat) (age1:A -> option A)  :=
{ af_unage : forall x x' y', level x' = level y' -> age1 x = Some x' -> exists y, age1 y = Some y'
; af_level1 : forall x, age1 x = None <-> level x = 0
; af_level2 : forall x y, age1 x = Some y -> level x = S (level y)
}.

Implicit Arguments af_unage [[A] [level] [age1]].
Implicit Arguments af_level1 [[A] [level] [age1]].
Implicit Arguments af_level2 [[A] [level] [age1]].

Class ageable (A:Type) := mkAgeable
{ level : A -> nat
; age1 : A -> option A
; age_facts : ageable_facts A level age1
}.
Definition age {A} `{ageable A} (x y:A) := age1 x = Some y.
Definition necR   {A} `{ageable A} : relation A := clos_refl_trans A age.
Delimit Scope pred with pred.
Local Open Scope pred.

Definition hereditary {A} (R:A->A->Prop) (p:A->Prop) :=
  forall a a':A, R a a' -> p a -> p a'.

Definition pred (A:Type) {AG:ageable A} :=
  { p:A -> Prop | hereditary age p }.

Bind Scope pred with pred.

Definition app_pred {A} `{ageable A} (p:pred A) : A -> Prop := proj1_sig p.
Definition pred_hereditary `{ageable} (p:pred A) := proj2_sig p.
Coercion app_pred : pred >-> Funclass.
Global Opaque pred.

Definition derives {A} `{ageable A} (P Q:pred A) := forall a:A, P a -> Q a.
Implicit Arguments derives.

Program Definition andp {A} `{ageable A} (P Q:pred A) : pred A :=
   fun a:A => P a /\ Q a.
Next Obligation.
  intros; intro; intuition;  apply pred_hereditary with a; auto.
Qed.

Program Definition imp {A} `{ageable A} (P Q:pred A) : pred A :=
   fun a:A => forall a':A, necR a a' -> P a' -> Q a'.
Next Obligation.
  intros; intro; intuition.
  apply H1; auto.
  apply rt_trans with a'; auto.
  apply rt_step; auto.
Qed.

Program Definition allp {A} `{ageable A} {B: Type} (f: B -> pred A) : pred A
  := fun a => forall b, f b a.
Next Obligation.
  intros; intro; intuition.
  apply pred_hereditary with a; auto.
  apply H1.
Qed.

Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : pred.
Notation "P '|--' Q" := (derives P Q) (at level 80, no associativity).
Notation "'All'  x ':' T  ',' P " := (allp (fun x:T => P%pred)) (at level 65, x at level 99) : pred.

Lemma forall_pred_ext  {A} `{agA : ageable A}: forall B P Q,
 (All x : B, (P x <--> Q x)) |-- (All x : B, P x) <--> (All x: B, Q x).
Abort.

End B.
