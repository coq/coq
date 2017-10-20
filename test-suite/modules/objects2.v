(* Check that non logical object loading is done after registration of
   the logical objects in the environment
*)

(* BZ#1118 (simplified version), submitted by Evelyne Contejean
  (used to failed in pre-V8.1 trunk because of a call to lookup_mind
   for structure objects)
*)

Module Type S. Record t : Set := { a : nat; b : nat }. End S.
Module Make (X:S). Module Y:=X. End Make.
