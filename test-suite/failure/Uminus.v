(* Check that the encoding of system U- fails *)

Inductive prop : Prop := down : Prop -> prop.

(* Coq should reject the following access of a Prop buried inside
   a prop. *)

Fail Definition up (p:prop) : Prop := let (A) := p in A.

(* Otherwise, we would have a proof of False via Hurkens' paradox *)

Axiom Hurkens_NoRetractFromSmallPropositionToProp_paradox :
  forall (bool : Prop) (p2b : Prop -> bool) (b2p : bool -> Prop),
    (forall A : Prop, b2p (p2b A) -> A) ->
    (forall A : Prop, A -> b2p (p2b A)) -> forall B : Prop, B.

Fail Definition paradox : False :=
 Hurkens_NoRetractFromSmallPropositionToProp_paradox
   prop
   down
   up
   (fun (A:Prop) (x:up (down A)) => (x:A))
   (fun (A:Prop) (x:A) => (x:up (down A)))
   False.
