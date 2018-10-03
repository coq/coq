(* This checks an error message as reported in bug #2172 *)

Axiom axiom : forall (E F : nat), E = F.
Lemma test : forall (E F : nat), E = F.
Proof.
  intros.
(* This used to raise the following non understandable error message:

   Error: Unable to find an instance for the variable x

   The reason this error was that rewrite generated the proof

   "eq_ind ?A ?x ?P ? ?y (axiom ?E ?F)"

   and the equation ?x=?E was solved in the way ?E:=?x leaving ?x
   unresolved. A stupid hack for solve this consisted in ordering
   meta=meta equations the other way round (with most recent evars
   instantiated first - since they are assumed to come first from the
   user in rewrite/induction/destruct calls).
*)
  Fail rewrite <- axiom.
