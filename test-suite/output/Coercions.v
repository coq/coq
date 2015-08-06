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
Print x.  (* This seems like a bug, but this is more of a misfeature: the
  rationale is that the external coercion cannot be inferred with no context. *)
Print x'.  (* This shows that within the context of id, both coercion levels
  are printed as quotes. *)

(* Has to set Printing Coercions before any Mode is effectively activated. *)
Set Printing Coercions.

Set Printing Coercions Mode "Quoted".
Check "Mode = Quoted".

Check a : C.
Print x.
Print x'.

Check a.
Check ““a”” : C.
Check ““a” : B” : C.

Check List.app (Some a) nil.

Set Printing Coercions Mode "Cast".
Check "Mode = Cast".

Check a : C.
Print x.
Print x'.

Check a.
Check ““a”” : C.
Check ““a” : B” : C.

Check List.app (Some a) nil.

Check "Printing All".
Set Printing All.

Check QuotedCoercion g false (QuotedCoercion f false a).

Unset Printing All.

Set Printing Coercions Mode "Quoted".

Notation "“f x ”" := (@QuotedCoercion _ _ (@f) false x) (at level 0,
  format "“f  x ”").

Notation "“g x ”" := (@QuotedCoercion _ _ (@g) false x) (at level 0,
  format "“g  x ”").

Check "Mode = Quoted + notations for specific coercions".
Check a : C.
Print x.
Print x'.

(* Why doesn't it display as “g “f _””, as above? *)
Check QuotedCoercion g false (QuotedCoercion f false a).

End testQuotedCoercions.
