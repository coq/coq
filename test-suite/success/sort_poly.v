Set Universe Polymorphism.

Module Syntax.
  Fail Definition foo@{| Set < Set } := Set.

  Definition foo@{u| Set < u} := Type@{u}.

  Definition bar@{s | u | Set < u} := Type@{u}.
  Set Printing Universes.
  Print bar.

  Definition baz@{s | | } := Type@{s | Set}.
  Print baz.

  Definition potato@{s | + | } := Type.

  Check eq_refl : Prop = baz@{Prop | }.

  Inductive bob@{s| |} : Prop := .
End Syntax.

Module Reduction.

  Definition qsort@{s | u |} := Type@{s | u}.

  Monomorphic Universe U.

  Definition tU := Type@{U}.
  Definition qU := qsort@{Type | U}.

  Definition q1 := Eval lazy in qU.
  Check eq_refl : q1 = tU.

  Definition q2 := Eval vm_compute in qU.
  Check eq_refl : q2 = tU.

  Definition q3 := Eval native_compute in qU.
  Check eq_refl : q3 = tU.

  Definition exfalso@{s|u|} (A:Type@{s|u}) (H:False) : A := match H with end.

  Definition exfalsoVM := Eval vm_compute in exfalso@{Type|Set}.
  Definition exfalsoNative := Eval native_compute in exfalso@{Type|Set}.

  Fixpoint iter@{s|u|} (A:Type@{s|u}) (f:A -> A) n x :=
    match n with
    | 0 => x
    | S k => iter A f k (f x)
    end.

  Definition iterType := Eval lazy in iter@{Type|_}.
  Definition iterSProp := Eval lazy in iter@{SProp|_}.

End Reduction.

Module Conversion.

  Inductive Box@{s|u|} (A:Type@{s|u}) := box (_:A).

  Definition t1@{s|u|} (A:Type@{s|u}) (x y : A) := box _ x.
  Definition t2@{s|u|} (A:Type@{s|u}) (x y : A) := box _ y.

  Fail Check eq_refl : t1 nat = t2 nat.
  Check fun A:SProp => eq_refl : t1 A = t2 A.

  Definition t (A:SProp) := Eval lazy in t1 A.

  Axiom v@{s| |} : forall (A:Type@{s|Set}), bool -> A.
  Fail Check fun P (x:P (v@{Type|} nat true)) => x : P (v nat false).
  Check fun (A:SProp) P (x:P (v A true)) => x : P (v A false).

End Conversion.

Module Inference.
  Definition zog@{s| |} (A:Type@{s|Set}) := A.

  (* implicit instance of zog gets a variable which then gets unified with s from the type of A *)
  Definition zag@{s| |} (A:Type@{s|Set}) := zog A.

  (* implicit type of A gets unified to Type@{s|Set} *)
  Definition zig@{s| |} A := zog@{s|} A.

  (* Unfortunately casting a hole to a sort (while typing A on the
     left of the arrow) produces a rigid univ level. It gets a
     constraint "= Set" but rigids don't get substituted away for (bad)
     reasons. This is why we need the 2 "+". *)
  Definition zig'@{s| + | +} A := A -> zog@{s|} A.

  (* different manually bound sort variables don't unify *)
  Fail Definition zog'@{s s'| |} (A:Type@{s|Set}) := zog@{s'|} A.
End Inference.

Module Inductives.
  (* TODO sort variable in the output sort *)
  Fail Inductive foo1@{s| |} : Type@{s|Set} := .

  Inductive foo2@{s| |} := Foo2 : Type@{s|Set} -> foo2.

  Inductive foo3@{s| |} (A:Type@{s|Set}) := Foo3 : A -> foo3 A.

  Fail Inductive foo4@{s|u v|v < u} : Type@{v} := C (_:Type@{s|u}).

  Inductive foo5@{s| |} (A:Type@{s|Set}) : Prop := Foo5 (_ : A).
  Definition foo5_ind'@{s| |} : forall (A : Type@{s|Set}) (P : Prop), (A -> P) -> foo5 A -> P
    := foo5_ind.

  (* TODO more precise squashing *)
  Fail Definition foo5_Prop_rect (A:Prop) (P:foo5 A -> Type)
    (H : forall a, P (Foo5 A a))
    (f : foo5 A)
    : P f
    := match f with Foo5 _ a => H a end.

  Set Primitive Projections.
  Set Warnings "+records".

  (* the SProp instantiation may not be primitive so the whole thing must be nonprimitive *)
  Fail Record R1@{s| |} : Type@{s|Set} := {}.

  (* the Type instantiation may not be primitive *)
  Fail Record R2@{s| |} (A:SProp) : Type@{s|Set} := { R2f1 : A }.

  (* R3@{SProp Type|} may not be primitive  *)
  Fail Record R3@{s s'| |} (A:Type@{s|Set}) : Type@{s'|Set} := { R3f1 : A }.

  (* TODO sort variable in output sort *)
  Fail Record R4@{s| |} (A:Type@{s|Set}) : Type@{s|Set} := { R4f1 : A}.

  (* non SProp instantiation must be squashed *)
  Fail Record R5@{s| |} (A:Type@{s|Set}) : SProp := { R5f1 : A}.
  Fail #[warnings="-non-primitive-record"]
    Record R5@{s| |} (A:Type@{s|Set}) : SProp := { R5f1 : A}.
  #[warnings="-non-primitive-record,-cannot-define-projection"]
    Record R5@{s| |} (A:Type@{s|Set}) : SProp := { R5f1 : A}.
  Fail Check R5f1.
  Definition R5f1_sprop (A:SProp) (r:R5 A) : A := let (f) := r in f.
  Fail Definition R5f1_prop (A:Prop) (r:R5 A) : A := let (f) := r in f.

  Record R6@{s| |} (A:Type@{s|Set}) := { R6f1 : A; R6f2 : nat }.
  Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:Prop) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f2 _) = Conversion.box _ y.(R6f2 _).

  #[projections(primitive=no)] Record R7@{s| |} (A:Type@{s|Set}) := { R7f1 : A; R7f2 : nat }.
  Check R7@{SProp|} : SProp -> Set.
  Check R7@{Type|} : Set -> Set.

End Inductives.
