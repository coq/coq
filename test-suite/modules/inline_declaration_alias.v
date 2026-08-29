(* An inlining declaration is a property of a module type, and must not be
   inherited by the modules implementing it. Here [F]'s parameter type declares
   [n] inlinable; [Inner] is an alias of the parameter, and the declaration used
   to be carried over to [Inner.n] and, through the [Include] and the
   [with Module], all the way to [MT'], whose use as a functor parameter type
   then asked for the body of [A.M.Sub.Inner.n]. That constant does not exist,
   [A.M.Sub.Inner] being an alias of [M1], and the application below was
   rejected with "The field n is missing in ...". *)

Module Type T. Parameter n : bool. End T.
Module M1. Definition n := false. End M1.

Module Type TI. Parameter Inline n : bool. End TI.
Module F (X : TI). Definition n := X.n. Module Inner := X. End F.

Module E. Module Sub := F M1. Definition n := Sub.n. End E.
Module B (Y : T). Module IY := Y. End B.
Module R. Include B E. End R.

Module Type MT. Declare Module M : T. End MT.
Module Type MT' := MT with Module M := R.IY.
Module A : MT'. Module M := R.IY. End A.

Module G (X : MT'). End G.
Module R2 := G A.
