(* -*- coq-prog-args: ("-top" "UnivBinders"); -*- *)

Set Universe Polymorphism.
Set Printing Universes.
(* Unset Strict Universe Declaration. *)

(* universe binders on inductive types and record projections *)
Inductive Empty@{uu} : Type@{uu} := .
Print Empty.

Set Primitive Projections.
Record PWrap@{uu} (A:Type@{uu}) := pwrap { punwrap : A }.
Print PWrap.
Print punwrap.

Unset Primitive Projections.
Record RWrap@{uu} (A:Type@{uu}) := rwrap { runwrap : A }.
Print RWrap.
Print runwrap.

(* universe binders also go on the constants for operational typeclasses. *)
Class Wrap@{uu} (A:Type@{uu}) := wrap : A.
Print Wrap.
Print wrap.

(* Instance in lemma mode used to ignore the binders. *)
#[global]
Instance bar@{uu} : Wrap@{uu} Set. Proof. exact nat. Qed.
Print bar.

Unset Strict Universe Declaration.
(* The universes in the binder come first, then the extra universes in
   order of appearance. *)
Definition foo@{uu +} := Type -> Type@{v} -> Type@{uu}.
Print foo.

Check Type@{i} -> Type@{j}.

Eval cbv in Type@{i} -> Type@{j}.

Set Strict Universe Declaration.

(* Binders even work with monomorphic definitions! *)
Monomorphic Definition mono@{uu} := Type@{uu}.
Print mono.
Check mono.
Check Type@{mono.uu}.

Module mono.
  Fail Monomorphic Universe uu.
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

Monomorphic Constraint Set < UnivBinders.mono.uu.

Module mono2.
  Monomorphic Universe uu.
End mono2.

Fail Monomorphic Definition mono2@{uu} := Type@{uu}.

Module SecLet.
  Unset Universe Polymorphism.
  Section fooS.
    (* Fail Let foo@{} := Type@{uu}. (* doesn't parse: Let foo@{...} doesn't exist *) *)

    Unset Strict Universe Declaration.
    (* the names used disappear, and fresh names are generated instead of exposing raw ints *)
    Let tt : Type@{uu} := Type@{v}.
    #[clearbody] Let ff : Type@{uu}. Proof. exact Type@{v}. Defined.
    Definition bobmorane := tt -> ff.
  End fooS.
  Print bobmorane.
End SecLet.

(* fun x x => foo is nonsense with local binders *)
Fail Definition fo@{uu uu} := Type@{uu}.

(* Using local binders for printing. *)
Print foo@{E M N}.
(* Underscores discard the name if there's one. *)
Print foo@{_ _ _}.
(* Can use a name for multiple universes *)
Print foo@{u u IMPORTANT}.

(* Also works for inductives and records. *)
Print Empty@{E}.
Print PWrap@{E}.

(* Also works for About. *)
About punwrap@{K}.

(* Instance length check. *)
Fail Print foo@{E}.
Fail Print mono@{E}.

(* Not everything can be printed with custom universe names. *)
Fail Print Stdlib.Init.Logic@{E}.

(* Nice error when constraints are impossible. *)
Monomorphic Universes gU gV. Monomorphic Constraint gU < gV.
Fail Lemma foo'@{u v|u < gU, gV < v, v < u} : nat.

Section SomeSec.
  Universe uu.
  Definition insec@{v} := Type@{uu} -> Type@{v}.
  Print insec.

  Inductive insecind@{k} := inseccstr : Type@{k} -> insecind.
  Print insecind.
End SomeSec.
Print insec.
Print insecind.

Section SomeSec2.
  Universe u.
  Definition insec2@{} := Prop.
End SomeSec2.
Print insec2.

Module SomeMod.
  Definition inmod@{uu} := Type@{uu}.
  Print inmod.
End SomeMod.
Print SomeMod.inmod.
Import SomeMod.
Print inmod.

Module Type SomeTyp. Definition inmod := Type. End SomeTyp.
Module SomeFunct (In : SomeTyp).
  Definition infunct@{uu v} := In.inmod@{uu} -> Type@{v}.
End SomeFunct.
Module Applied := SomeFunct(SomeMod).
Print Applied.infunct.

(* Multi-axiom declaration

   In polymorphic mode the domain Type gets separate universes for the
   different axioms, but all axioms have to declare all universes. In
   monomorphic mode they also get separate universes. *)
Axiom axfoo@{i+} axbar : Type -> Type@{i}.
Monomorphic Axiom axfoo'@{i+} axbar' : Type -> Type@{i}.

About axfoo. About axbar. About axfoo'. About axbar'.

Print axfoo. Print axbar. Print axfoo'. Print axbar'.

Fail Axiom failfoo failbar@{i} : Type.

(* Notation interaction *)
Module Notas.
  Unset Universe Polymorphism.
  Module Import M. Universe i. End M.

  Polymorphic Definition foo@{i} := Type@{M.i} -> Type@{i}.
  Print foo. (* must not print Type@{i} -> Type@{i} *)

End Notas.

Module NoAutoNames.
  Monomorphic Universe u0.

  (* The anonymous universe doesn't get a name (names are only
     invented at the end of a definition/inductive) so no need to
     qualify u0. *)
  Check (Type@{u0} -> Type).

End NoAutoNames.

(* Universe binders survive through compilation, sections and modules. *)
Require TestSuite.bind_univs.
Print bind_univs.mono.
Print bind_univs.poly.

Module MutualTypes.

Inductive MutualR1 (A:Type) := { p1 : MutualR2 A }
with MutualR2 (A:Type) := { p2 : MutualR1 A }.
Print MutualR1.

Inductive MutualI1 (A:Type) := C1 (p1 : MutualI2 A)
with MutualI2 (A:Type) := C2 (p2 : MutualI1 A).
Print MutualI1.

CoInductive MutualR1' (A:Type) := { p1' : MutualR2' A }
with MutualR2' (A:Type) := { p2' : MutualR1' A }.
Print MutualR1'.

CoInductive MutualI1' (A:Type) := C1' (p1 : MutualI2' A)
with MutualI2' (A:Type) := C2' (p2 : MutualI1' A).
Print MutualI2'.

End MutualTypes.

Module Inconsistency.

Set Universe Polymorphism.
Definition g@{a b} := Type@{a} : Type@{b}.
Fail Definition h@{a} := g@{a a}.

End Inconsistency.

Module PartialTemplate.

Set Implicit Arguments.
Unset Elimination Schemes.
Unset Universe Polymorphism.

Inductive JMeq (A:Type) (x:A) : forall B:Type, B -> Prop :=
    JMeq_refl : JMeq x x.

About JMeq.

End PartialTemplate.

Module Collision.
  Unset Universe Polymorphism.

  Module x.
    Universe u0.
    Definition a := Type@{u0}.
  End x.

  Fail Definition x@{u0} := Type@{u0}.
  Definition x := Type.

  Goal True.
    Fail
      let a := eval cbv in x.a in
      let b := eval cbv in x in
      constr_eq_strict a b.

    let a := eval cbv in Type@{x.u1} in
    let b := eval cbv in x in
    constr_eq_strict a b.
  Abort.
End Collision.

Module Schemes.
  Check eq_rect.
End Schemes.
