(* Unification error tests *)

Module A.

(* Check regression of an UNBOUND_REL bug *)
Inductive T := C : forall {A}, A -> T.
Fail Check fun x => match x return ?[X] with C a => a end.

(* Bug #3634 *)
Fail Check (id:Type -> _).

End A.
