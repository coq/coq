(* 1st-order unification did not work when in competition with pattern unif. *)

Set Implicit Arguments.
Lemma test : forall
  (A : Type)
  (B : Type)
  (f : A -> B)
  (S : B -> Prop)
  (EV : forall y (f':A->B), (forall x', S (f' x')) -> S (f y))
  (HS : forall x', S (f x'))
  (x : A),
  S (f x).
Proof.
  intros. eapply EV. intros. 
  (* worked in v8.2 but not in v8.3beta, fixed in r12898 *)
  apply HS.

  (* still not compatible with 8.2 because an evar can be solved in
     two different ways and is left open *)
