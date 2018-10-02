(* Check that resolved status of evars follows "restrict" *)

Axiom H : forall (v : nat), Some 0 = Some v -> True.
Lemma L : True.
eapply H with _;
match goal with
  | |- Some 0 = Some ?v => change (Some (0+0) = Some v)
end.
Abort.

(* The original example *)

Set Default Proof Using "Type".

Module heap_lang.

Inductive expr :=
  | InjR (e : expr).

Inductive val :=
  | InjRV (v : val).

Bind Scope val_scope with val.

Fixpoint of_val (v : val) : expr :=
  match v with
  | InjRV v => InjR (of_val v)
  end.

Fixpoint to_val (e : expr) : option val := None.

End heap_lang.
Export heap_lang.

Module W.
Inductive expr :=
  | Val (v : val)
  (* Sums *)
  | InjR (e : expr).

Fixpoint to_expr (e : expr) : heap_lang.expr :=
  match e with
  | Val v => of_val v
  | InjR e => heap_lang.InjR (to_expr e)
  end.

End W.



Section Tests.

  Context (iProp: Type).
  Context (WPre: expr -> Prop).

  Context (tac_wp_alloc :
             forall (e : expr) (v : val),
               to_val e = Some v -> WPre e).

  Lemma push_atomic_spec (x: val) :
    WPre (InjR (of_val x)).
  Proof.
(* This works. *)
eapply tac_wp_alloc with _.
match goal with
  | |- to_val ?e = Some ?v =>
    change (to_val (W.to_expr (W.InjR (W.Val x))) = Some v)
end.
Undo. Undo.
(* This is fixed *)
eapply tac_wp_alloc with _;
match goal with
  | |- to_val ?e = Some ?v =>
    change (to_val (W.to_expr (W.InjR (W.Val x))) = Some v)
end.
Abort.
