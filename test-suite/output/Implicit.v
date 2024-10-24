Set Implicit Arguments.
Unset Strict Implicit.

(* Suggested by Pierre Casteran (BZ#169) *)
(* Argument 3 is needed to typecheck and should be printed *)
Definition compose (A B C : Set) (f : A -> B) (g : B -> C) (x : A) := g (f x).
Check (compose (C:=nat) S).

(* Better to explicitly display the arguments inferable from a
   position that could disappear after reduction *)
Inductive ex (A : Set) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P.
Check (ex_intro (P:=fun _ => True) (x:=0) I).

(* Test for V8 printing of implicit by names *)
Definition d1 y x (h : x = y :>nat) := h.
Definition d2 x := d1 (y:=x).

Print d2.

Set Strict Implicit.
Unset Implicit Arguments.

(* Check maximal insertion of implicit *)

Require Import TestSuite.list.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Definition id (A:Type) (x:A) := x.

Check map id (1::nil).

Definition id' (A:Type) (x:A) := x.

Arguments id' {A} x.

Check map id' (1::nil).

Unset Maximal Implicit Insertion.
Unset Implicit Arguments.

(* Check explicit insertion of last non-maximal trailing implicit to ensure *)
(* correct arity of partiol applications *)

Set Implicit Arguments.
Definition id'' (A:Type) (x:A) := x.

Check map (@id'' nat) (1::nil).

Module MatchBranchesInContext.

Set Implicit Arguments.
Set Contextual Implicit.

Inductive option A := None | Some (a:A).
Coercion some_nat := @Some nat.
Check fix f x := match x with 0 => None | n => some_nat n end.

End MatchBranchesInContext.

Module LetInContext.

Set Implicit Arguments.
Set Contextual Implicit.
Axiom False_rect : forall A:Type, False -> A.
Check fun x:False => let y:= False_rect (A:=bool) x in y. (* will not be in context: explicitation *)
Check fun x:False => let y:= False_rect (A:=True) x in y. (* will be in context: no explicitation *)

End LetInContext.
