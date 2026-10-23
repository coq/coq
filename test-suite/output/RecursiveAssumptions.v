(* Test for Print Assumptions with recursive type traversal *)

(* Test case 1: Simple axiom depending on another axiom in its type *)
Axiom A : Prop.
Axiom B : A -> Prop.
Definition C := B.

(* Print Assumptions now includes both B and A *)
Print Assumptions C.

(* Test case 2: Axiom with type depending on function type *)
Axiom P : Type.
Axiom Q : P -> Prop.
Axiom R : forall x, Q x.

(* Testing with a theorem *)
Lemma test : forall x, Q x.
Proof. exact R. Qed.

Print Assumptions test.

(* Test case 3: No axioms - should show "Closed under the global context" *)
Definition simple := 1 + 1.

Print Assumptions simple.

Set Printing Assumptions Per Reference.
Print Assumptions C test simple.
