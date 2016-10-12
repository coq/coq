Module bt.
Require Import Equivalence.

Record Equ (A : Type) (R : A -> A -> Prop).
Definition equiv {A} R (e : Equ A R) := R.
Record Refl (A : Type) (R : A -> A -> Prop).
Axiom equ_refl : forall A R (e : Equ A R), Refl _ (@equiv A R e).
Hint Extern 0 (Refl _ _) => unshelve class_apply @equ_refl; [shelve|] : foo.

Variable R : nat -> nat -> Prop.
Lemma bas : Equ nat R.
Admitted.
Hint Resolve bas : foo.
Hint Extern 1 => match goal with |- (_ -> _ -> Prop) => shelve end : foo.

Goal exists R, @Refl nat R.
  eexists.
  Set Typeclasses Debug.
  (* Fail solve [unshelve eauto with foo]. *)
  Set Typeclasses Debug Verbosity 1.
  Test Typeclasses Depth.
  solve [typeclasses eauto with foo].
Qed.

(* Set Typeclasses Compatibility "8.5". *)
Parameter f : nat -> Prop.
Parameter g : nat -> nat -> Prop.
Parameter h : nat -> nat -> nat -> Prop.
Axiom a : forall x y, g x y -> f x -> f y.
Axiom b : forall x (y : Empty_set), g (fst (x,y)) x.
Axiom c : forall x y z, h x y z -> f x -> f y.
Hint Resolve a b c : mybase.
Goal forall x y z, h x y z -> f x -> f y.
  intros.
  Set Typeclasses Debug.
  typeclasses eauto with mybase.
  Unshelve.
Abort.
End bt.
Generalizable All Variables.

Module mon.

Reserved Notation "'return' t" (at level 0).
Reserved Notation "x >>= y" (at level 65, left associativity).



Record Monad {m : Type -> Type} := {
  unit : forall {α}, α -> m α where "'return' t" := (unit t) ;
  bind : forall {α β}, m α -> (α -> m β) -> m β where "x >>= y" := (bind x y) ;
  bind_unit_left : forall {α β} (a : α) (f : α -> m β), return a >>= f = f a }.

Print Visibility.
Print unit.
Implicit Arguments unit [[m] [m0] [α]].
Implicit Arguments Monad [].
Notation "'return' t" := (unit t).

(* Test correct handling of existentials and defined fields. *)

Class A `(e: T) := { a := True }.
Class B `(e_: T) := { e := e_; sg_ass :> A e }.

Set Typeclasses Debug.

Goal forall `{B T}, Prop.
  intros. apply a.
Defined.

Goal forall `{B T}, Prop.
  intros. refine (@a _ _ _).
Defined.

Class B' `(e_: T) := { e' := e_; sg_ass' :> A e_ }.

Goal forall `{B' T}, a.
  intros. exact I.
Defined.

End mon.

(* Correct treatment of dependent goals *) 

(* First some preliminaries: *)

Section sec.
  Context {N: Type}.
  Class C (f: N->N) := {}.
  Class E := { e: N -> N }.
  Context
    (g: N -> N) `(E) `(C e)
    `(forall (f: N -> N), C f -> C (fun x => f x))
    (U: forall f: N -> N, C f -> False).

(* Now consider the following: *)

  Let foo := U (fun x => e x).
  Check foo _.

(* This type checks fine, so far so good. But now
 let's try to get rid of the intermediate constant foo.
 Surely we can just expand it inline, right? Wrong!: *)
 Check U (fun x => e x) _.
End sec.

Module IterativeDeepening.

  Class A.
  Class B.
  Class C.

  Instance: B -> A | 0.
  Instance: C -> A | 0.
  Instance: C -> B -> A | 0.
  Instance: A -> A | 0.
  
  Goal C -> A.
    intros.
    Set Typeclasses Debug.
    Fail Timeout 1 typeclasses eauto.
    Set Typeclasses Iterative Deepening.
    Fail typeclasses eauto 1.
    typeclasses eauto 2.
    Undo.
    Unset Typeclasses Iterative Deepening.
    Fail Timeout 1 typeclasses eauto.
    Set Typeclasses Iterative Deepening.
    typeclasses eauto.
  Qed.

End IterativeDeepening.
