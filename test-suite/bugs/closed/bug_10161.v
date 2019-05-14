Inductive SwitchT (A : Type) : Type :=
| switchT : forall T, SwitchT T -> SwitchT A.

Set Printing Universes.

Fail Inductive UseSwitchT :=
| useSwitchT : SwitchT UseSwitchT -> UseSwitchT.
(* used to stack overflow, should be univ inconsistency cannot satisfy u = u+1 *)
