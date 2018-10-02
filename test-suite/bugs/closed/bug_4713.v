Module Type T.
  Parameter t : Type.
End T.
Module M : T.
  Definition t := unit.
End M.

Fail Module Z : T with Module t := M := M.
Fail Module Z <: T with Module t := M := M.
Fail Declare Module Z : T with Module t := M.
