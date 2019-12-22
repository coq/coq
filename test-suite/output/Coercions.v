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

(* Implicit arguments and coercions *)

Axiom h : nat -> forall {A} {_:list A}, bool.
Coercion h : nat >-> Funclass.
Check @h 0 _ (@nil bool).
Arguments h _ {A} _.
Check 0 (1::nil)%list.
Check 0 : list nat -> bool.
Check 1 : list nat -> bool. (* bidirectional typing *)

(* Nested coercions and notations *)

Module NestedCoercionsNotation.

Axiom expr : Type.
Axiom val : Type.
Axiom Val : val -> expr.
Axiom assert : val.
Axiom Rec : nat -> expr.
Axiom App : expr -> expr -> expr.
Coercion Val : val >-> expr.
Coercion App : expr >-> Funclass.
(* A notation where the coercions are absent *)
Notation "'assert:' e" := (assert (Rec e)) (at level 10).
Check assert: 0.

End NestedCoercionsNotation.
