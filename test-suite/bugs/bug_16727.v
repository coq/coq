Require Import Setoid.

Axiom R : unit -> unit -> Prop.
Axiom RP : forall a b, R a b -> Prop.

Lemma RiemannInt_P2 :
  forall (a b: unit) (vn: R a b) (wn : R a a),
   RP a a wn ->
    { l:unit | True }.
Proof.
intros a b vn.
try rewrite vn.
Abort.
