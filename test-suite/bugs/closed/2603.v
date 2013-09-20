(** Namespace of module vs. namescope of definitions/constructors/...

As noticed by A. Appel in bug #2603, module names and definition
names used to be in the same namespace. But conflict with names
of constructors (or 2nd mutual inductive...) used to not be checked
enough, leading to stange situations.

- In 8.3pl3 we introduced checks that forbid uniformly the following
  situations.

- For 8.4 we finally managed to make module names and other names
  live in two separate namespace, hence allowing all of the following
  situations.
*)

Module Type T.
End T.

Declare Module K : T.

Module Type L.
Declare Module E : T.
End L.

Module M1 : L with Module E:=K.
Module E := K.
Inductive t := E. (* Used to be accepted, but End M1 below was failing *)
End M1.

Module M2 : L with Module E:=K.
Inductive t := E.
Module E := K. (* Used to be accepted *)
End M2. (* Used to be accepted *)
