Require Export NumPrelude.
Require Export NZAxioms.

Set Implicit Arguments.

Module Type NAxiomsSig.
Declare Module Export NZOrdAxiomsMod : NZOrdAxiomsSig.
Open Local Scope NatIntScope.

Notation N := NZ (only parsing).
Notation E := NZE (only parsing).

Parameter Inline recursion : forall A : Set, A -> (N -> A -> A) -> N -> A.
Implicit Arguments recursion [A].

Axiom pred_0 : P 0 == 0.

Axiom recursion_wd : forall (A : Set) (EA : relation A),
  forall a a' : A, EA a a' ->
    forall f f' : N -> A -> A, eq_fun2 E EA EA f f' ->
      forall x x' : N, x == x' ->
        EA (recursion a f x) (recursion a' f' x').

Axiom recursion_0 :
  forall (A : Set) (a : A) (f : N -> A -> A), recursion a f 0 = a.

Axiom recursion_succ :
  forall (A : Set) (EA : relation A) (a : A) (f : N -> A -> A),
    EA a a -> fun2_wd E EA EA f ->
      forall n : N, EA (recursion a f (S n)) (f n (recursion a f n)).

End NAxiomsSig.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
