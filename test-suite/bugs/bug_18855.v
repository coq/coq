(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

#[universes(polymorphic)] Inductive I@{q|u|} (A : Type@{q|u}) (a : A) : Type@{u} := C.

Inductive Sbool : SProp := strue | sfalse.

Universe u.

Symbol raise raise2 raise3 : forall A : Type@{u}, A.

Symbol a b : unit.

Rewrite Rule raise_pi := raise (forall (x : ?A), ?B) >-> raise2 (forall (x : ?A), ?B).
Rewrite Rule raise2_pi := raise2 (forall (x : ?A), ?B) >-> raise3 (forall (x : ?A), ?B).
Rewrite Rule raise_pi' := raise (forall (x : I _ match a with tt => _ end), ?B) >-> 0.

Check eq_refl :
    raise (I _ match b with tt => strue end -> unit) = raise3 (I _ match b with tt => strue end -> unit).
