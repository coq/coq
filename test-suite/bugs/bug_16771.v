Require Import CRelationClasses.

Structure ConstructiveReals : Type :=
  {
    CRcarrier : Prop;
    CRle (x y : CRcarrier) := False;
  }.

#[local] Hint Resolve iff_equivalence : mydb.

Goal forall {R : ConstructiveReals},
    CRelationClasses.Equivalence (CRle R).
Proof.
intros.
auto with mydb.
(* Anomaly "in Univ.repr: Universe Top.169 undefined."
Please report at http://coq.inria.fr/bugs/.*)
Abort.
