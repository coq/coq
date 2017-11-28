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

(* fun x x => foo is nonsense with local binders *)
Fail Definition fo@{u u} := Type@{u}.

(* Using local binders for printing. *)
Print foo@{E M N}.
(* Underscores discard the name if there's one. *)
Print foo@{_ _ _}.

(* Also works for inductives and records. *)
Print Empty@{E}.
Print PWrap@{E}.

(* Also works for About. *)
About punwrap@{K}.

(* Instance length check. *)
Fail Print foo@{E}.
Fail Print mono@{E}.

(* Not everything can be printed with custom universe names. *)
Fail Print Coq.Init.Logic@{E}.

(* Nice error when constraints are impossible. *)
Monomorphic Universes gU gV. Monomorphic Constraint gU < gV.
Fail Lemma foo@{u v|u < gU, gV < v, v < u} : nat.

(* Universe binders survive through compilation, sections and modules. *)
Require bind_univs.
Print bind_univs.mono.
Print bind_univs.poly.

Section SomeSec.
  Universe u.
  Definition insec@{v} := Type@{u} -> Type@{v}.
  Print insec.
End SomeSec.
Print insec.

Module SomeMod.
  Definition inmod@{u} := Type@{u}.
  Print inmod.
End SomeMod.
Print SomeMod.inmod.
Import SomeMod.
Print inmod.

Module Type SomeTyp. Definition inmod := Type. End SomeTyp.
Module SomeFunct (In : SomeTyp).
  Definition infunct@{u v} := In.inmod@{u} -> Type@{v}.
End SomeFunct.
Module Applied := SomeFunct(SomeMod).
Print Applied.infunct.

(* Multi-axiom declaration

   In polymorphic mode the domain Type gets separate universes for the
   different axioms, but all axioms have to declare all universes. In
   polymorphic mode they get the same universes, ie the type is only
   interpd once. *)
Axiom axfoo@{i+} axbar : Type -> Type@{i}.
Monomorphic Axiom axfoo'@{i+} axbar' : Type -> Type@{i}.

About axfoo. About axbar. About axfoo'. About axbar'.

Fail Axiom failfoo failbar@{i} : Type.
