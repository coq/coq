(*i $Id: i*)
Require Export Axioms.
Require Export LeProps.

(*s Axiomatizing [>] from [<] *)


Axiom not_le_gt : (x,y:N)~(x<=y)->(x>y).
Axiom gt_not_le : (x,y:N)(x>y)->~(x<=y).

Hints Resolve not_le_gt : num.

Hints Immediate gt_not_le : num.
