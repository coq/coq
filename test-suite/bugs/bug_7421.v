

Universe i j.

Goal False.
Proof.
  Check Type@{i} : Type@{j}.
  Fail constr_eq_strict Type@{i} Type@{j}.
  assert_succeeds constr_eq Type@{i} Type@{j}. (* <- i=j is forgotten after assert_succeeds *)
  Fail constr_eq_strict Type@{i} Type@{j}.

  constr_eq Type@{i} Type@{j}. (* <- i=j is retained *)
  constr_eq_strict Type@{i} Type@{j}.
  Fail Check Type@{i} : Type@{j}.

  Fail constr_eq Prop Set.
  Fail constr_eq Prop Type.

  Fail constr_eq_strict Type Type.
  constr_eq Type Type.

  constr_eq_strict Set Set.
  constr_eq Set Set.
  constr_eq Prop Prop.

  let x := constr:(Type) in constr_eq_strict x x.
  let x := constr:(Type) in constr_eq x x.

  Fail lazymatch type of prod with
       | ?A -> ?B -> _ => constr_eq_strict A B
       end.
  lazymatch type of prod with
  | ?A -> ?B -> _ => constr_eq A B
  end.
  lazymatch type of prod with
  | ?A -> ?B -> ?C => constr_eq A C
  end.

Abort.
