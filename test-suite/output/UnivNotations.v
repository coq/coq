Axiom foo : forall A:Type, A -> Type.

(* this test is about checking when Type in a notation is considered
   to match a term *)
Notation "! x" := (foo Type@{*} x) (at level 2).
Notation "# x" := (foo Univ x) (at level 2).

(* first with Printing Universes off *)

(* terms produced using the notation print using the notation  *)
Check ! nat.

(* Set does not match Type *)
Check foo Set nat.

Sort s.
Axiom S : Univ@{s;Set}.

(* rigid sorts (here global sort) do not match the notation's Univ *)
Check foo _ S.
Check # S.
Fail Check ! S.

Goal True.
Proof.
  (* sort unification variable matches Univ (and is printed as Univ in the [forall] annotation) *)
  (* NB don't use Check here as it collapses before printing (maybe this will change someday?) *)
  assert (forall A, A -> foo _ A). 2:trivial.
  Show.
Abort.

(* now with Printing Universes on *)
Set Printing Universes.

(* Printing Universes makes universes not match Type *)
Check ! nat.

(* global sort still doesn't match Type nor Univ *)
Check foo _ S.

Goal True.
Proof.
  (* sort unif variable doesn't match Type or Univ *)
  assert (forall A, A -> foo _ A). 2:trivial.
  Show.
Abort.
