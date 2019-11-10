(* -*- coq-prog-args: ("-type-in-type"); -*- *)

Inductive Ind : SProp := C : Ind -> Ind.
