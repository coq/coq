Set Implicit Arguments.
Unset Strict Implicit.
Parameter (M : nat -> Type).
Parameter (mp : forall (T1 T2 : Type) (f : T1 -> T2), list T1 -> list T2).

Definition foo (s : list {n : nat & M n}) :=
  let exT := existT in mp (fun x => projT1 x) s.
