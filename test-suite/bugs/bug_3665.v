(* File reduced by coq-bug-finder from original input, then from 5449 lines to 44 lines *)
(* coqc version trunk (September 2014) compiled on Sep 25 2014 2:53:46 with OCaml 4.01.0
   coqtop version trunk (September 2014) *)
Set Primitive Projections.

Axiom IsHSet : Type -> Type.
Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.

Module withdefault.
Canonical Structure default_HSet := fun T P => (@BuildhSet T P).
Goal forall (z : hSet) (T0 : Type -> Type),
       (forall (A : Type) (P : T0 A -> Type) (aa : T0 A), P aa) ->
       forall x0 : setT z, Set.
  clear; intros z T H.
  Set Debug Unification.
  Fail refine (H _ _). (* Timeout! *)
Abort.
End withdefault.

Module withnondefault.
Variable T0 : Type -> Type.
Variable T0hset: forall A, IsHSet (T0 A).

Canonical Structure nondefault_HSet := fun A =>(@BuildhSet (T0 A) (T0hset A)).
Canonical Structure default_HSet := fun A P =>(@BuildhSet A P).
Goal forall (z : hSet) (T0 : Type -> Type),
       (forall (A : Type) (P : T0 A -> Type) (aa : T0 A), P aa) ->
       forall x0 : setT z, Set.
  clear; intros z T H.
  Set Debug Unification.
  Fail refine (H _ _). (* Timeout! *)
Abort.
End withnondefault.
