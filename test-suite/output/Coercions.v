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

Axiom A : Type.
Axiom B : Type.
Axiom C : Type.
Axiom a : A.
Axiom f : A -> B.
Axiom g : B -> C.
Axiom id : C -> C.
Coercion f : A >-> B.
Coercion g : B >-> C.

Notation "“ x ”" := (QuotedCoercion x) (at level 0,
  format "“ x ”").

Check a : C.
Definition x := a : C.
Print x.  (* This seems to be a bug, but this more of a misfeature: the would-be
  rationale is that the external coercion cannot be inferred with no context. *)
Definition x' := id a.  (* This shows that within the context of id, both levels
  of coercion are printing as quotes. *)
Print x'.

End testQuotedCoercions.
