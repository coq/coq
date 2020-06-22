(* Unification error tests *)

Module A.

(* Check regression of an UNBOUND_REL bug *)
Inductive T := C : forall {A}, A -> T.
Fail Check fun x => match x return ?[X] with C a => a end.

(* Bug #3634 *)
Fail Check (id:Type -> _).

End A.

(* Choice of evar names *)

Goal (forall x, S (S (S x)) = x) -> exists x, S x = 0.
eexists.
rewrite H.
Show.
Undo 2.
eexists ?[x].
rewrite H.
Show.
Undo 2.
eexists ?[y].
rewrite H.
Show.
reflexivity.
Qed.

(* Preserve the name if there is one *)

Goal (forall x, S x = x) -> exists x, S x = 0.
eexists ?[y].
rewrite H.
Show.
reflexivity.
Qed.
