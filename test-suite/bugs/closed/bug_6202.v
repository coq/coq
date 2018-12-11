(* This was fixed at some time, suspectingly in PR #6328 *)

Inductive foo := F (a : forall var : Type -> Type, unit -> var unit) (_ : a = a).
Goal foo.
  eexists (fun var => fun u : unit => ltac:(clear u)).
  shelve.
  Unshelve.
  all:[ > | ].
  shelve.
  Fail Grab Existential Variables.
Abort.
