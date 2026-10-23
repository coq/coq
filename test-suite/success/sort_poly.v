Set Universe Polymorphism.

Module Syntax.
  Fail Definition foo@{| Set < Set } := Set.

  Definition foo@{u| Set < u} := Type@{u}.

  Definition bar@{s ; u | Set < u} := Type@{u}.
  Set Printing Universes.
  Print bar.

  Definition baz@{s ; } := Univ@{s ; Set}.
  Print baz.

  Definition potato@{s ; + } := Type.

  Check eq_refl : Prop = baz@{Prop ; }.

  Inductive bob@{s ; } : Prop := .
End Syntax.

Module Reduction.

  Definition qsort@{s ; u } := Univ@{s ; u}.

  Monomorphic Universe U.

  Definition tU := Type@{U}.
  Definition qU := qsort@{Type ; U}.

  Definition q1 := Eval lazy in qU.
  Check eq_refl : q1 = tU.

  Definition q2 := Eval vm_compute in qU.
  Check eq_refl : q2 = tU.

  Definition q3 := Eval native_compute in qU.
  Check eq_refl : q3 = tU.

  Definition exfalso@{s;u|} (A:Univ@{s;u}) (H:False) : A := match H with end.

  Definition exfalsoVM := Eval vm_compute in exfalso@{Type;Set}.
  Definition exfalsoNative := Eval native_compute in exfalso@{Type;Set}.

  Fixpoint iter@{s;u|} (A:Univ@{s;u}) (f:A -> A) n x :=
    match n with
    | 0 => x
    | S k => iter A f k (f x)
    end.

  Definition iterType := Eval lazy in iter@{Type;_}.
  Definition iterSProp := Eval lazy in iter@{SProp;_}.

End Reduction.

Module Conversion.

  Cumulative Inductive Box@{s;u|} (A:Univ@{s;u}) := box (_:A).

  Definition t1@{s;u|} (A:Univ@{s;u}) (x y : A) := box _ x.
  Definition t2@{s;u|} (A:Univ@{s;u}) (x y : A) := box _ y.

  Definition t1'@{s;u|} (A:Univ@{s;u}) (x y : A) := x.
  Definition t2'@{s;u|} (A:Univ@{s;u}) (x y : A) := y.

  Fail Check eq_refl : t1 nat = t2 nat.
  Fail Check eq_refl : t1' nat = t2' nat.

  Check fun A:SProp => eq_refl : t1 A = t2 A.
  Check fun A:SProp => eq_refl : box _ (t1' A) = box _ (t2' A).

  Fail Definition equi_eliminable@{s1 s2;|s1 -> s2, s2 -> s1} (A : Univ@{s1;Set}) : Univ@{s2;Set} := A.
  Fail Definition equi_eliminable@{s1 s2;|s1 -> s2, s2 -> s1} (A : Univ@{s2;Set}) : Univ@{s1;Set} := A.

  Definition ignore@{s;u|} {A:Univ@{s;u}} (x:A) := tt.
  Definition unfold_ignore@{s;u|} (A:Univ@{s;u}) : ignore (t1 A) = ignore (t2 A) := eq_refl.

  Definition t (A:SProp) := Eval lazy in t1 A.

  Axiom v@{s; |} : forall (A:Univ@{s;Set}), bool -> A.
  Fail Check fun P (x:P (v@{Type;} nat true)) => x : P (v nat false).
  Check fun (A:SProp) P (x:P (v A true)) => x : P (v A false).

End Conversion.

Module Inference.
  Definition zog@{s; |} (A:Univ@{s;Set}) := A.

  (* implicit instance of zog gets a variable which then gets unified with s from the type of A *)
  Definition zag@{s; |} (A:Univ@{s;Set}) := zog A.

  (* implicit type of A gets unified to Univ@{s;Set} *)
  Definition zig@{s; |} A := zog@{s;} A.

  (* Unfortunately casting a hole to a sort (while typing A on the
     left of the arrow) produces a rigid univ level. It gets a
     constraint "= Set" but rigids don't get substituted away for (bad)
     reasons. This is why we need the 2 "+". *)
  Definition zig'@{s; + | +} A := A -> zog@{s;} A.

  (* different manually bound sort variables don't unify *)
  Fail Definition zog'@{s s'; |} (A:Univ@{s;Set}) := zog@{s';} A.
End Inference.

Module Inductives.
  Inductive foo1@{s; |} : Univ@{s;Set} := .
  Fail Check foo1_sind.

  Definition foo1_False@{s;+|+} (x:foo1@{s;}) : False := match x return False with end.
  (* s ;  |= s -> Prop *)

  Inductive foo2@{s; |} := Foo2 : Univ@{s;Set} -> foo2.
  Check foo2_rect.

  Inductive foo3@{s; |} (A:Univ@{s;Set}) := Foo3 : A -> foo3 A.
  Check foo3_rect.

  Fail Inductive foo4@{s;u v|v < u} : Type@{v} := C (_:Univ@{s;u}).

  Inductive foo5@{s; |} (A:Univ@{s;Set}) : Prop := Foo5 (_ : A).
  Definition foo5_ind'@{s; |} : forall (A : Univ@{s;Set}) (P : Prop), (A -> P) -> foo5 A -> P
    := foo5_ind.

  (* TODO unify sort variable instead of failing *)
  Fail Definition foo5_Prop_rect (A:Prop) (P:foo5 A -> Type)
    (H : forall a, P (Foo5 A a))
    (f : foo5 A)
    : P f
    := match f with Foo5 _ a => H a end.
    (*
    Error: The quality constraints are inconsistent: cannot enforce Prop -> Type because it would identify Type and Prop which is inconsistent.
    This is introduced by the constraints Prop -> Type
    *)

  Definition foo5_Prop_rect (A:Prop) (P:foo5 A -> Type)
    (H : forall a, P (Foo5 A a))
    (f : foo5@{Prop;} A)
    : P f
    := match f with Foo5 _ a => H a end.

  (* all sort poly output with nonzero contructors are squashed (avoid interfering with uip) *)
  Inductive foo6@{s; |} : Univ@{s;Set} := Foo6.
  Fail Check foo6_sind.

  Definition foo6_rect@{s;+|+} (P:foo6@{s;} -> Type)
    (H : P Foo6)
    (f : foo6)
    : P f
    := match f with Foo6 => H end.
  (* s ; u |= s -> Type *)

  Definition foo6_prop_rect (P:foo6 -> Type)
    (H : P Foo6)
    (f : foo6@{Prop;})
    : P f
    := match f with Foo6 => H end.

  Definition foo6_type_rect (P:foo6 -> Type)
    (H : P Foo6)
    (f : foo6@{Type;})
    : P f
    := match f with Foo6 => H end.

  Definition foo6_qsort_rect@{s;u|} (P:foo6 -> Univ@{s;u})
    (H : P Foo6)
    (f : foo6@{s;})
    : P f
    := match f with Foo6 => H end.

  Fail Definition foo6_2qsort_rect@{s s';u|} (P:foo6 -> Univ@{s;u})
    (H : P Foo6)
    (f : foo6@{s';})
    : P f
    := match f with Foo6 => H end.
  (* The command has indeed failed with message:
     Elimination constraints are not implied by the ones declared:
     s' -> s *)

  Inductive foo7@{s; |} : Univ@{s;Set} := Foo7_1 | Foo7_2.
  Fail Check foo7_sind.
  Fail Check foo7_ind.

  Definition foo7_prop_ind (P:foo7 -> Prop)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop;})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  Fail Definition foo7_prop_rect (P:foo7 -> Type)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop;})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  Set Primitive Projections.
  Set Warnings "+records".

  (* the SProp instantiation may not be primitive so the whole thing must be nonprimitive *)
  Fail Record R1@{s; |} : Univ@{s;Set} := {}.

  (* the Type instantiation may not be primitive *)
  Fail Record R2@{s; |} (A:SProp) : Univ@{s;Set} := { R2f1 : A }.

  (* R3@{SProp Type|} may not be primitive  *)
  Fail Record R3@{s s'; |} (A:Univ@{s;Set}) : Univ@{s';Set} := { R3f1 : A }.

  Record R4@{s; |} (A:Univ@{s;Set}) : Univ@{s;Set} := { R4f1 : A}.

  (* non SProp instantiation must be squashed *)
  Fail Record R5@{s; |} (A:Univ@{s;Set}) : SProp := { R5f1 : A}.
  #[warnings="-non-primitive-record"]
    Record R5@{s; |} (A:Univ@{s;Set}) : SProp := { R5f1 : A}.
  Definition R5f1_sprop (A:SProp) (r:R5 A) : A := let (f) := r in f.
  Fail Definition R5f1_prop (A:Prop) (r:R5 A) : A := let (f) := r in f.

  Record R6@{s; |} (A:Univ@{s;Set}) := { R6f1 : A; R6f2 : nat }.
  Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:Prop) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:SProp) (x y : R6 A) =>
          eq_refl : Conversion.box _ x.(R6f2 _) = Conversion.box _ y.(R6f2 _).

  #[projections(primitive=no)] Record R7@{s; |} (A:Univ@{s;Set}) := { R7f1 : A; R7f2 : nat }.
  Check R7@{SProp;} : SProp -> Set.
  Check R7@{Type;} : Set -> Set.

  Inductive sigma@{s;u v|} (A:Univ@{s;u}) (B:A -> Univ@{s;v}) : Univ@{s;max(u,v)}
    := pair : forall x : A, B x -> sigma A B.

  Definition sigma_srect@{s;k +|} A B
    (P : sigma@{s;_ _} A B -> Univ@{s;k})
    (H : forall x b, P (pair _ _ x b))
    (s:sigma A B)
    : P s
    := match s with pair _ _ x b => H x b end.

  (* squashed because positive type with >0 constructors *)
  Fail Definition sigma_srect'@{s sk;k +|} A B
    (P : sigma@{s;_ _} A B -> Univ@{sk;k})
    (H : forall x b, P (pair _ _ x b))
    (s:sigma A B)
    : P s
    := match s with pair _ _ x b => H x b end.

  (* even though it's squashed, we can still define the projections *)
  Definition pr1@{s;+|} {A B} (s:sigma@{s;_ _} A B) : A
    := match s with pair _ _ x _ => x end.

  Definition pr2@{s;+|} {A B} (s:sigma@{s;_ _} A B) : B (pr1 s)
    := match s with pair _ _ _ y => y end.

  (* And we can prove eta with implicit elaboration of elimination constraints.
    We can't prove eta without the constraints. *)
  Inductive seq@{s;u|} (A:Univ@{s;u}) (a:A) : A -> Prop := seq_refl : seq A a a.
  Arguments seq_refl {_ _}.

  Definition eta@{s;+|+} A B (s:sigma@{s;_ _} A B) : seq _ s (pair A B (pr1 s) (pr2 s)).
  Proof.
    destruct s. simpl. reflexivity.
  Qed.

  (* sigma as a primitive record works better *)
  Cumulative Record Rsigma@{s;u v|} (A:Univ@{s;u}) (B:A -> Univ@{s;v}) : Univ@{s;max(u,v)}
    := Rpair { Rpr1 : A; Rpr2 : B Rpr1 }.

  (* match desugared to primitive projections using definitional eta *)
  Definition Rsigma_srect@{s sk;k +|} A B
    (P : Rsigma@{s;_ _} A B -> Univ@{sk;k})
    (H : forall x b, P (Rpair _ _ x b))
    (s:Rsigma A B)
    : P s
    := match s with Rpair _ _ x b => H x b end.

  (* sort polymorphic exists (we could also make B sort poly)
     can't be a primitive record since the first projection isn't defined at all sorts *)
  Inductive sexists@{s;u|} (A:Univ@{s;u}) (B:A -> Prop) : Prop
    := sexist : forall a:A, B a -> sexists A B.

  (* we can eliminate to Prop *)
  Check sexists_ind.

  Cumulative Inductive sigma3@{s s' s'';u v| } (A:Univ@{s;u}) (P:A -> Univ@{s';v}) :
    Univ@{s'';max(u,v)} :=
    exist3 : forall x:A, P x -> sigma3 A P.

  Arguments exist3 {_ _}.

  Definition π1@{s s';u v|} {A:Univ@{s;u}} {P:A -> Univ@{s';v}} (p : sigma3@{_ _ Type;_ _} A P) : A :=
    match p return A with exist3 a _ => a end.

End Inductives.
