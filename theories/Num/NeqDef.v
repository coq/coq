(*i $Id $ i*)

(*s DisEquality is defined as the negation of equality *)

Require Params.
Require EqParams.
Require EqAxioms.

Definition neq : N -> N -> Prop := [x,y] ~(x=y).
Infix 6 "<>" neq.

(* Proofs of axioms *)
Lemma eq_not_neq : (x,y:N)x=y->~(x<>y).
Unfold neq; Auto with num.
Save.
Hints Immediate eq_not_neq : num.

Lemma neq_sym : (x,y:N)(x<>y)->(y<>x).
Unfold neq; Auto with num.
Save.
Hints Resolve neq_sym : num.

Lemma neq_not_neq_trans : (x,y,z:N)(x<>y)->~(y<>z)->(x<>z).
Unfold neq; EAuto with num.
Save.
Hints Resolve neq_not_neq_trans : num.




