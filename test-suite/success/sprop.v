(* -*- mode: coq; coq-prog-args: ("-allow-sprop") -*- *)

Check SProp.

Definition iUnit : SProp := forall A : SProp, A -> A.
Definition itt : iUnit := fun A a => a.

Definition iSquash (A:Type) : SProp
  := forall P : SProp, (A -> P) -> P.
Definition isquash A : A -> iSquash A
  := fun a P f => f a.

Fail Check (fun A : SProp => A : Type).

Lemma foo : Prop.
Proof. pose (fun A : SProp => A : Type). Abort.

(* define evar as product *)
Check (fun (f:(_:SProp)) => f _).
