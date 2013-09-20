(* Check that the encoding of system U- fails *)

Require Hurkens.

Inductive prop : Prop := down : Prop -> prop.

(* Coq should reject the following access of a Prop buried inside
   a prop. *)

Fail Definition up (p:prop) : Prop := let (A) := p in A.

(* Otherwise, we would have a proof of False via Hurkens' paradox *)

Fail Definition paradox : False :=
 Hurkens.NoRetractFromSmallPropositionToProp.paradox
   prop
   down
   up
   (fun (A:Prop) (x:up (down A)) => (x:A))
   (fun (A:Prop) (x:A) => (x:up (down A)))
   False.
