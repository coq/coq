Require Import TestSuite.admit.
Fixpoint exp (n : nat) (T : Set)
  := match n with
       | 0 => T
       | S n' => exp n' (T * T)
     end.
Definition big := Eval compute in exp 13 nat.
Module NonPrim.
  Unset Primitive Projections.
  Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
  Definition x : sigT (fun x => x).
  Proof.
    exists big; admit.
  Defined.
  Goal True.
    pose ((fun y => y = y) (projT1 _ x)) as y.
    Time cbv beta in y. (* 0s *)
    admit.
  Defined.
End NonPrim.
Module Prim.
  Set Primitive Projections.
  Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
  Definition x : sigT (fun x => x).
  Proof.
    exists big; admit.
  Defined.
  Goal True.
    pose ((fun y => y = y) (projT1 _ x)) as y.
    Timeout 1 cbv beta in y. (* takes around 2s.  Grows with the value passed to [exp] above *)
    admit.
  Defined.
End Prim.
