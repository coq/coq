
Inductive expr :=
| Const: nat -> expr
| Add: expr -> expr -> expr.

Inductive eval: expr -> expr -> Prop :=
| EConst: forall n,
    eval (Const n) (Const n)
| EAdd: forall e1 v1 e2 v2,
    eval e1 (Const v1) ->
    eval e2 (Const v2) ->
    eval (Add e1 e2) (Const (v1 + v2)).

Coercion Const: nat >-> expr.

Lemma eval_total: forall e, exists v, eval e v.
Proof.
  induction e.
  - admit.
  - destruct IHe1 as [v1 IH1].
    eexists.
    eapply EAdd.
    + exact IH1.
Abort.
