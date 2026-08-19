(* The checks a module operation skipped are recorded on the module it
   produced: the constant an inlined body came from is gone (#12155), and the
   operation's own subtyping checks belong to no declaration (#16646). *)

Module Type T1.
  Parameter Inline foo : Set.
End T1.
Module Impl1.
  Unset Universe Checking.
  Definition foo : Set := Set.
  Set Universe Checking.
End Impl1.
Module F1 (X : T1).
  Definition foo := X.foo.
End F1.
(* #12155: the inlined body was checked with universe checking off. *)
Module M1 := F1 Impl1.

Module Type T2.
  Parameter t : Set.
End T2.
Module F2 (X : T2).
  Definition u : Set := X.t.
End F2.
Module Impl2.
  Definition t := Set.
End Impl2.

(* #16646: the application itself ran with universe checking off. *)
Unset Universe Checking.
Module M2 := F2 Impl2.
Set Universe Checking.

(* The same through Include ... *)
Module M3.
  Unset Universe Checking.
  Include F2 Impl2.
  Set Universe Checking.
End M3.

(* ... and through sealing. *)
Unset Universe Checking.
Module M4 : T2 := Impl2.
Set Universe Checking.

(* Not only universes: an inlined body accepted with the guard condition off. *)
Module Type T5.
  Parameter Inline f : nat -> nat.
End T5.
Module Impl5.
  Unset Guard Checking.
  Fixpoint f (n : nat) : nat := f n.
  Set Guard Checking.
End Impl5.
Module F5 (X : T5).
  Definition g := X.f.
End F5.
Module M5 := F5 Impl5.

(* With every check on there is nothing to record. *)
Module Impl6.
  Definition t : Set := nat.
End Impl6.
Module M6 := F2 Impl6.
