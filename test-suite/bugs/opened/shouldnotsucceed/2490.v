Class Rel A := rel : A -> Prop.
Class Rel2 A := rel2 : A -> Prop.
Class Property A (o : A -> Prop) := rel_property : True.

Class Op A := op : A -> A.
Instance my_op {A} {r : Rel A} {p : Property A r} : Op A := fun x => x.

Section test.
Context A (r2 : Rel2 A) (p2 : Property A r2).

(* 8.3 yields an error: "Could not find an instance for "Op A" in environment".
  Trunk, on the other hand, uses [r2] as an instance of [Rel] and hence finds
the previously defined instance of [Op]. Trunk's behavior is incorrect. *)
Lemma test (x : A) : op x = op x.
Admitted.

(* If we don't refer to the canonical name, Coq will actually complain, as it
should. *)
Lemma test (x : A) : my_op x = my_op x.

End test.

(* Now we make an instance of [Op] without dependent condition. *)
Instance my_op_nondep {A} {r : Rel A} : Op A := fun x => x.

Section test2.
Context A (r2 : Rel2 A).

