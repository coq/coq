(* Interaction between coercions and casts *)
(*   Example provided by Eduardo Gimenez   *)

Parameter Z,S:Set.

Parameter f: S  -> Z.
Coercion  f: S >-> Z.

Parameter g : Z -> Z.

Check [s](g (s::S)).
