(* Submitted by Randy Pollack *)

Record pred (S : Set) : Type :=  {sp_pred :> S -> Prop}.
Record rel (S : Set) : Type :=  {sr_rel :> S -> S -> Prop}.

Section testSection.
Variables (S : Set) (P : pred S) (R : rel S) (x : S).
Check (P x).
Check (R x x).
End testSection.

(* Check the removal of coercions with target Funclass *)

Record foo : Type :=  {D :> nat -> nat}.
Check (fun (x : foo) (n : nat) => x n).

(* Check both removal of coercions with target Funclass and mixing
   string and numeral scopes *)

Require Import String.
Open Scope string_scope.
Inductive PAIR := P (s:string) (n:nat).
Coercion P : string >-> Funclass.
Check ("1" 0).

(* Check quoting coercions *)

Section testQuotedCoercions.

Require Import List.

Axiom A : Type.
Axiom B : Type.
Axiom C : Type.
Axiom a : A.
Axiom f : A -> B.
Axiom g : B -> C.
Axiom h : forall A, option A -> list A.
Axiom id : C -> C.
Coercion f : A >-> B.
Coercion g : B >-> C.
Coercion h : option >-> list.

Definition x := a : C.
Definition x' := id a.

Check "No Printing option".
Check a : C.
Print x.
Print x'.

Set Printing Coercions Quoted.

Check "Printing Coercions Quoted".
Check a : C.
Print x.  (* This seems to be a bug, but this more of a misfeature: the would-be
  rationale is that the external coercion cannot be inferred with no context. *)
Print x'.  (* This shows that within the context of id, both levels of coercion
  are printing as quotes. *)

Check a.
Check ““a”” : C.
Check ““a” : B” : C.

Check List.app (Some a) nil.

Set Printing Coercions.

Check "Printing Coercions Quoted + Printing Coercions".
Check a : C.
Print x.
Print x'.

Unset Printing Coercions Quoted.

Check "Printing Coercions".
Check a : C.
Print x.
Print x'.

Unset Printing Coercions.

Check "No Printing option again".
Check a : C.
Print x.
Print x'.

Check "Printing All".
Set Printing All.

Check QuotedCoercion g (QuotedCoercion f a).

Unset Printing All.

Notation "“ x ↑ T ”" := (@QuotedCoercion _ T _ x) (at level 0,
  format "“ x  ↑  T ”").

Set Printing Coercions Quoted.

Check "Printing Coercions Quoted + uparrow".
Check a : C.
Print x.
Print x'.

Check QuotedCoercion g (QuotedCoercion f a).

Notation "“f x ”" := (@QuotedCoercion _ _ (@f) x) (at level 0,
  format "“f  x ”").

Notation "“g x ”" := (@QuotedCoercion _ _ (@g) x) (at level 0,
  format "“g  x ”").

Check "Printing Coercions Quoted + notations for specific coercions".
Check a : C.
Print x.
Print x'.

(* I would like this to display with “f _” as above, not with “_ ↑ _”. *)
Check QuotedCoercion g (QuotedCoercion f a).

End testQuotedCoercions.
