Section FreeMonad.

  Variable S : Type.
  Variable P : S -> Type.

  Inductive FreeF A : Type :=
  | retFree : A -> FreeF A
  | opr     : forall s, (P s -> FreeF A) -> FreeF A.

End FreeMonad.

Section Fibonnacci.

  Inductive gen_op := call_op : nat -> gen_op.
  Definition gen_ty (op : gen_op) :=
    match op with
    | call_op _ => nat
    end.

  Fail Definition fib0 (n:nat) : FreeF gen_op gen_ty nat :=
    match n  with
    | 0
    | 1 => retFree _ _ _ 1
    | S (S k) =>
      opr _ _ _ (call_op (S k))
          (fun r1 => opr _ _ _ (call_op k)
                      (fun r0 => retFree (* _ _ _ *) (r1 + r0)))
    end.

End Fibonnacci.
