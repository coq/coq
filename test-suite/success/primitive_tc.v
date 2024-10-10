Create HintDb test discriminated.

(* Testing that projections can be made hint opaque. *)
Module ProjOpaque.
  #[projections(primitive)]
  Record bla := { x : unit }.

  Definition bli := {| x := tt |}.

  Class C (p : unit) := {}.
  Definition I  : C (x bli) := Build_C _.

  #[local] Hint Resolve I : test.
  #[local] Hint Opaque x : test.

  Goal C tt.
  Proof.
    Fail typeclasses eauto with test.
  Abort.
End ProjOpaque.

(* Testing that compatibility constants are equated with their projections in
   the bnet. *)
Module CompatConstants.
  Class T (p : Prop) : Prop := {}.

  Axiom prod : Prop -> Prop -> Prop.
  Axiom T_prod : forall p1 p2, T p1 -> T p2 -> T (prod p1 p2).
  Axiom T_True : T True.

  Class F (f : unit -> Prop) : Prop := { F_T :: forall u, T (f u) }.

  #[projections(primitive)]
  Record R (useless : unit) : Type :=
    { v : unit -> Prop;
      v_F : F (v);
    }.
  Hint Opaque v : test.
  Hint Resolve v_F F_T T_prod T_True : test.

  (* Notation constant := (@v tt). *)

  Goal forall (a : R tt) q, T (prod (v _ a q) (True)).
  Proof.
    intros a.
    (* [v _ a] gets turned into its compatibility constant by the application
       of [T_prod]. The application of [v_F] after [F_T] only works if the
       bnet correctly equates the compatibility constant with the projection
       used in the type and pattern of [v_F] *)
    typeclasses eauto with test.
  Qed.
End CompatConstants.

(* Testing that projection opacity settings are properly discharged at the end
   of sections. *)
Module Sections.
  #[local] Hint Constants Opaque : test.
  #[local] Hint Projections Opaque : test.
  Class C (u : unit) := {}.
  Definition i : C tt := Build_C _.
  #[global] Hint Resolve i : test.

  Section S.
    Context (P : Prop).  (* Load bearing [Context] but content does not matter! *)
    #[projections(primitive)]
    Record r := R { v : unit; prf : P }. (* Load bearing use of the [Context] *)
    #[global] Hint Transparent v : test.
    Definition x (p: P) := {| v := tt; prf := p|}.
    #[global] Hint Transparent x : test.
    Print HintDb test. (* [v] is transparent *)
    Goal forall p, C (v (x p)).
    Proof. intros.
      typeclasses eauto with test. (* [i] is a candidate, [v] must be transparent *)
    Qed.
  End S.
  Print HintDb test. (* [v] is reportedly transparent *)
  Goal forall P (p : P), C (v P (x P p)).
  Proof. intros.
    typeclasses eauto with test. (* This will fail if [Hint Transparent v] is improperly discharged. *)
  Qed.
End Sections.

Module HintExtern.
  #[projections(primitive)]
  Record bi (x : True) : Type := BI {car : Type; foo : car}.
  Axiom x : True.
  Axiom PROP:bi x.
  Inductive Fwd (P : car x PROP) : Prop := MKFWD.
  Create HintDb db discriminated.
  #[local] Hint Opaque foo : test.
  Module ConstantPattern.
    #[local] Hint Extern 0 (Fwd (@foo x PROP)) => constructor : test.
    Goal Fwd (@foo x PROP).
    Proof.
      intros.
      typeclasses eauto with test.
    Qed.
  End ConstantPattern.

  Module ProjPattern.
    #[local] Hint Extern 0 (Fwd (PROP.(@foo x))) => constructor : test.
    Goal Fwd (@foo x PROP).
    Proof.
      intros.
      typeclasses eauto with test.
    Qed.
  End ProjPattern.
End HintExtern.
