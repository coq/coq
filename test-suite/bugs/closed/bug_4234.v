Definition UU := Type.

Definition dirprodpair {X Y : UU} := existT (fun x : X => Y).

Definition funtoprodtoprod {X Y Z : UU} : { a : X -> Y & X -> Z }.
Proof.
  refine (dirprodpair _ (fun x => _)).
