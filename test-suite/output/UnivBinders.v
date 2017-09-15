Set Universe Polymorphism.
Set Printing Universes.
Unset Strict Universe Declaration.

(* universe binders on inductive types and record projections *)
Inductive Empty@{u} : Type@{u} := .
Print Empty.

Set Primitive Projections.
Record PWrap@{u} (A:Type@{u}) := pwrap { punwrap : A }.
Print PWrap.
Print punwrap.

Unset Primitive Projections.
Record RWrap@{u} (A:Type@{u}) := rwrap { runwrap : A }.
Print RWrap.
Print runwrap.

(* universe binders also go on the constants for operational typeclasses. *)
Class Wrap@{u} (A:Type@{u}) := wrap : A.
Print Wrap.
Print wrap.

(* Instance in lemma mode used to ignore the binders. *)
Instance bar@{u} : Wrap@{u} Set. Proof. exact nat. Qed.
Print bar.

(* The universes in the binder come first, then the extra universes in
   order of appearance. *)
Definition foo@{u +} := Type -> Type@{v} -> Type@{u}.
Print foo.

(* Binders even work with monomorphic definitions! *)
Monomorphic Definition mono@{u} := Type@{u}.
Print mono.
