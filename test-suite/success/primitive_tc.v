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
