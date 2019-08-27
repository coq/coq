(* -*- coq-prog-args: ("-top" "UnivBinders"); -*- *)

Set Universe Polymorphism.
Set Printing Universes.
(* Unset Strict Universe Declaration. *)

(* universe binders on inductive types and record projections *)
Inductive Empty@{u} : Type@{u} := .
Print Term Empty.

Set Primitive Projections.
Record PWrap@{u} (A:Type@{u}) := pwrap { punwrap : A }.
Print Term PWrap.
Print Term punwrap.

Unset Primitive Projections.
Record RWrap@{u} (A:Type@{u}) := rwrap { runwrap : A }.
Print Term RWrap.
Print Term runwrap.

(* universe binders also go on the constants for operational typeclasses. *)
Class Wrap@{u} (A:Type@{u}) := wrap : A.
Print Term Wrap.
Print Term wrap.

(* Instance in lemma mode used to ignore the binders. *)
Instance bar@{u} : Wrap@{u} Set. Proof. exact nat. Qed.
Print Term bar.

Unset Strict Universe Declaration.
(* The universes in the binder come first, then the extra universes in
   order of appearance. *)
Definition foo@{u +} := Type -> Type@{v} -> Type@{u}.
Print Term foo.

Check Type@{i} -> Type@{j}.

Eval cbv in Type@{i} -> Type@{j}.

Set Strict Universe Declaration.

(* Binders even work with monomorphic definitions! *)
Monomorphic Definition mono@{u} := Type@{u}.
Print Term mono.
Check mono.
Check Type@{mono.u}.

Module mono.
  Fail Monomorphic Universe u.
  Monomorphic Universe MONOU.

  Monomorphic Definition monomono := Type@{MONOU}.
  Check monomono.

  Monomorphic Inductive monoind@{i} : Type@{i} := .
  Monomorphic Record monorecord@{i} : Type@{i} := mkmonorecord {}.
End mono.
Check mono.monomono. (* qualified MONOU *)
Import mono.
Check monomono. (* unqualified MONOU *)
Check mono. (* still qualified mono.u *)

Monomorphic Constraint Set < UnivBinders.mono.u.

Module mono2.
  Monomorphic Universe u.
End mono2.

Fail Monomorphic Definition mono2@{u} := Type@{u}.

Module SecLet.
  Unset Universe Polymorphism.
  Section foo.
    (* Fail Let foo@{} := Type@{u}. (* doesn't parse: Let foo@{...} doesn't exist *) *)
    Unset Strict Universe Declaration.
    Let tt : Type@{u} := Type@{v}. (* names disappear in the ether *)
    Let ff : Type@{u}. Proof. exact Type@{v}. Qed. (* names disappear into space *)
    Definition bobmorane := tt -> ff.
  End foo.
  Print Term bobmorane.
End SecLet.

(* fun x x => foo is nonsense with local binders *)
Fail Definition fo@{u u} := Type@{u}.

(* Using local binders for printing. *)
Print Term foo@{E M N}.
(* Underscores discard the name if there's one. *)
Print Term foo@{_ _ _}.

(* Also works for inductives and records. *)
Print Term Empty@{E}.
Print Term PWrap@{E}.

(* Also works for About. *)
About punwrap@{K}.

(* Instance length check. *)
Fail Print Term foo@{E}.
Fail Print Term mono@{E}.

(* Not everything can be printed with custom universe names. *)
Fail Print Term Coq.Init.Logic@{E}.

(* Nice error when constraints are impossible. *)
Monomorphic Universes gU gV. Monomorphic Constraint gU < gV.
Fail Lemma foo@{u v|u < gU, gV < v, v < u} : nat.

(* Universe binders survive through compilation, sections and modules. *)
Require TestSuite.bind_univs.
Print Term bind_univs.mono.
Print Term bind_univs.poly.

Section SomeSec.
  Universe u.
  Definition insec@{v} := Type@{u} -> Type@{v}.
  Print Term insec.

  Inductive insecind@{k} := inseccstr : Type@{k} -> insecind.
  Print Term insecind.
End SomeSec.
Print Term insec.
Print Term insecind.

Section SomeSec2.
  Universe u.
  Definition insec2@{} := Prop.
End SomeSec2.
Print Term insec2.

Module SomeMod.
  Definition inmod@{u} := Type@{u}.
  Print Term inmod.
End SomeMod.
Print Term SomeMod.inmod.
Import SomeMod.
Print Term inmod.

Module Type SomeTyp. Definition inmod := Type. End SomeTyp.
Module SomeFunct (In : SomeTyp).
  Definition infunct@{u v} := In.inmod@{u} -> Type@{v}.
End SomeFunct.
Module Applied := SomeFunct(SomeMod).
Print Term Applied.infunct.

(* Multi-axiom declaration

   In polymorphic mode the domain Type gets separate universes for the
   different axioms, but all axioms have to declare all universes. In
   polymorphic mode they get the same universes, ie the type is only
   interpd once. *)
Axiom axfoo@{i+} axbar : Type -> Type@{i}.
Monomorphic Axiom axfoo'@{i+} axbar' : Type -> Type@{i}.

About axfoo. About axbar. About axfoo'. About axbar'.

Fail Axiom failfoo failbar@{i} : Type.
