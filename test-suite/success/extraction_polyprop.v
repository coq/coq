(* The current extraction cannot handle this situation,
   and shouldn't try, otherwise it might produce some Ocaml
   code that segfaults. See Table.error_singleton_become_prop
   or S. Glondu's thesis for more details. *)

Require Coq.extraction.Extraction.

Definition f {X} (p : (nat -> X) * True) : X * nat :=
  (fst p 0, 0).

Definition f_prop := f ((fun _ => I),I).

Fail Extraction f_prop.
