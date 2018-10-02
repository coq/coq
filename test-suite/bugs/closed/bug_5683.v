Require Import Program.Tactics.
Require Import FunctionalExtensionality.

Inductive Succ A :=
| Succ_O : Succ A
| Succ_S : A -> Succ A.
Arguments Succ_O {A}.
Arguments Succ_S {A} _.

Inductive Zero : Type :=.

Inductive ty :=
| ty_nat : ty
| ty_arr : ty -> ty -> ty.

Inductive term A :=
| term_abs : ty -> term (Succ A) -> term A
| term_app : term A -> term A -> term A
| term_var : A -> term A
| term_nat : nat -> term A.
Arguments term_abs {A} _ _.
Arguments term_app {A} _ _.
Arguments term_var {A} _.
Arguments term_nat {A} _.

Class Functor F :=
{
  ret : forall {A}, A -> F A;
  fmap : forall {A B}, (A -> B) -> F A -> F B;
  fmap_id : forall {A} (fa : F A), fmap (@id A) fa = fa;
  fmap_compose : forall {A B C} (fa : F A) (g : B -> C) (h : A -> B), fmap (fun
a => g (h a)) fa = fmap g (fmap h fa)
}.

Class Monad M `{Functor M} :=
{
  bind : forall {A B}, M A -> (A -> M B) -> M B;
  ret_left_id : forall {A B} (a : A) (f : A -> M B), bind (ret a) f = f a;
  ret_right_id : forall {A} (m : M A), bind m ret = m;
  bind_assoc : forall {A B C} (m : M A) (f : A -> M B) (g : B -> M C), bind
(bind m f) g = bind m (fun x => bind (f x) g)
}.

Instance Succ_Functor : Functor Succ.
Proof.
  unshelve econstructor.
  - intros A B f fa.
    destruct fa.
    + apply Succ_O.
    + apply Succ_S. tauto.
  - intros. apply Succ_S. assumption.
  - intros A [|a]; reflexivity.
  - intros A B C [|a] g h; reflexivity.
Defined.

(* Anomaly: Not an arity *)
Program Fixpoint term_bind {A B} (tm : term A) (f : A -> term B) : term B :=
    let Succ_f (var : Succ A) :=
        match var with
        | Succ_O => term_var Succ_O
        | Succ_S var' => _
        end in
    match tm with
    | term_app tm1 tm2 => term_app (term_bind tm1 f) (term_bind tm2 f)
    | term_abs ty body => term_abs ty (term_bind body Succ_f)
    | term_var a => f a
    | term_nat n => term_nat n
    end.
Next Obligation.
  intros.
Admitted.
