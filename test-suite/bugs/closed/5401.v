(* Testing printing of bound unnamed variables in pattern printer *)

Module A.
Parameter P : nat -> Type.
Parameter v : forall m, P m.
Parameter f : forall (P : nat -> Type), (forall a, P a) -> P 0.
Class U (R : P 0) (m : forall x, P x) : Prop.
Instance w : U (f _ (fun _ => v _)) v.
Print HintDb typeclass_instances.
End A.

(* #5731 *)

Module B.
Axiom rel : Type -> Prop.
Axiom arrow_rel : forall {A1}, A1 -> rel A1.
Axiom forall_rel : forall E, (forall v1 : Type, E v1 -> rel v1) -> Prop.
Axiom inl_rel: forall_rel _ (fun _ => arrow_rel).
Hint Resolve inl_rel : foo.
Print HintDb foo.
End B.
