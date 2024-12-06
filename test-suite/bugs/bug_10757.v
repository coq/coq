From Corelib.Program Require Import Wf.
Require Import Extraction ExtrOcamlBasic.
Print sig.
Section FIXPOINT.

Variable A: Type.

Variable eq: A -> A -> Prop.
Variable beq: A -> A -> bool.
Hypothesis beq_eq: forall x y, beq x y = true -> eq x y.
Hypothesis beq_neq: forall x y, beq x y = false -> ~eq x y.

Variable le: A -> A -> Prop.
Hypothesis le_trans: forall x y z, le x y -> le y z -> le x z.

Definition gt (x y: A) := le y x /\ ~eq y x.
Hypothesis gt_wf: well_founded gt.

Variable F: A -> A.
Hypothesis F_mon: forall x y, le x y -> le (F x) (F y).

Program Fixpoint iterate
    (x: A) (PRE: le x (F x)) (SMALL: forall z, le (F z) z -> le x z)
    {wf gt x}
    : {y : A | eq y (F y) /\ forall z, le (F z) z -> le y z } :=
  let x' := F x in
  match beq x x' with
  | true  => x
  | false => iterate x' _ _
  end.
Next Obligation.
  split.
- auto.
- apply beq_neq. auto.
Qed.

End FIXPOINT.

Recursive Extraction iterate.
