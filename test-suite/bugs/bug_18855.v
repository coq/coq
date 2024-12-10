(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

#[universes(polymorphic)] Inductive I@{q| |} (A : Type@{q|Set}) (a : A) : Set := C.

Inductive sbool : SProp := strue | sfalse.

Universe u.

Symbol raise : forall A : Type@{u}, A.

Rewrite Rule raise_pi := raise (forall (x : ?A), ?B) => fun x => raise ?B.

Definition a : id (let x : sbool := (fun _ => match sfalse with strue => strue | sfalse => sfalse end) tt in (raise (I _ x -> unit), I _ x))
   = id (fun _ : I sbool sfalse => raise unit, I sbool strue) := eq_refl.
