Module M.
(* The encapsulation in a module tests that the grammar rules
   and keywords are correctly registered *)
Require Derive.
End M.

(* Tests when x is refined by typechecking *)
Derive x in (eq_refl x = eq_refl 0) as x_ok.
reflexivity.
Qed.

Derive s in (forall z, eq_refl (s z) = eq_refl (S z)) as s_ok.
reflexivity.
Qed.

Derive foo : nat in (foo = foo) as bar.
Proof.
reflexivity.
Unshelve.
exact 0.
Qed.

Derive id : (forall {A}, A -> A) in (forall {A} (a:A), id a = a) as spec.
Proof.
unfold id.
reflexivity.
Qed.
About id.
Check id 0.

Set Universe Polymorphism.

(* An example with no polymorphic universe constraints in the witness *)
Derive id' : (forall {A}, A -> A) in (forall {A} (a:A), id' a = a) as spec'.
Proof.
Unshelve.
2: exact (fun A a => a).
reflexivity.
Qed.

(* An example with polymorphic universe constraints in the witness *)
Derive id'' : (forall {A}, A -> A) in (forall {A} (a:A), id'' a = a) as spec''.
Proof.
unfold id''.
reflexivity.
Qed.

Check id'@{Set} 0.
