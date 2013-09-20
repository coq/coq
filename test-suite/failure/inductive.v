(* A check that sort-polymorphic product is not set too low *)

Inductive prod (A B:Type) : Type := pair : A -> B -> prod A B.
Fail Check (fun (A:Type) (B:Prop) => (prod A B : Prop)).
Fail Check (fun (A:Prop) (B:Type) => (prod A B : Prop)).

(* Check that the nested inductive types positivity check avoids recursively
   non uniform parameters (at least if these parameters break positivity) *)

Inductive t (A:Type) : Type := c : t (A -> A) -> t A.
Fail Inductive u : Type := d : u | e : t u -> u.

(* This used to succeed in versions 8.1 to 8.3 *)

Require Import Logic.
Require Hurkens.
Definition Ti := Type.
Inductive prod2 (X Y:Ti) := pair2 : X -> Y -> prod2 X Y.
Fail Definition B : Prop := let F := prod2 True in F Prop. (* Aie! *)
(*Definition p2b (P:Prop) : B := pair2 True Prop I P.
Definition b2p (b:B) : Prop := match b with pair2 _ P => P end.
Lemma L1 : forall A : Prop, b2p (p2b A) -> A.
Proof (fun A x => x).
Lemma L2 : forall A : Prop, A -> b2p (p2b A).
Proof (fun A x => x).
Check Hurkens.paradox B p2b b2p L1 L2.*)

