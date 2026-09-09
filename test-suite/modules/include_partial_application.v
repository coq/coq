(* An [Include] need not supply every argument of the functor it applies: the
   remaining parameters are instantiated with the module being built, as for an
   unapplied functor ([Include Self]). Applying [F] to the fields [R] has
   accumulated is what makes the second parameter below. The elaboration of the
   inclusion used to assume a total application and destructed the result as a
   structure, failing with "Module F of ... not expected to be a functor". *)

Module Type T. Parameter n : bool. End T.
Module F (X : T) (Y : T). Definition m := X.n. End F.
Module M. Definition n := true. End M.

Module R.
  Include M.
  Include F M.
End R.

(* The same shape is what Stdlib's Numbers/Natural/Abstract/NLog.v uses. *)
Module Type ST (X : T) (Y : T). Parameter q : bool. End ST.
Module Type U. Include T. Include ST M. End U.
