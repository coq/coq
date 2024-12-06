From Corelib Require Import ssreflect.

Axiom blah : forall (P : unit -> Type) (n : unit), P n.

Lemma t (r := True): True.
Fail elim /blah: r.
(* Anomaly
"File "plugins/ssr/ssrcommon.ml", line 792, characters 18-24: Assertion failed."
Please report at http://coq.inria.fr/bugs/. *)
Abort.
