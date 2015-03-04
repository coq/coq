Set Primitive Projections.

CoInductive stream A := { hd : A; tl : stream A }.

CoFixpoint ticks : stream unit :=
  {| hd := tt; tl := ticks |}.

Arguments hd [ A ] s.
Arguments tl [ A ] s.

CoInductive bisim {A} : stream A -> stream A -> Prop :=
  | bisims s s' : hd s = hd s' -> bisim (tl s) (tl s') -> bisim s s'.

Lemma bisim_refl {A} (s : stream A) : bisim s s.
Proof.
  revert s.
  cofix aux. intros. constructor. reflexivity. apply aux.
Defined.

Lemma constr : forall (A : Type) (s : stream A),
    bisim s (Build_stream _ s.(hd) s.(tl)).
Proof.
  intros. constructor. reflexivity. simpl. apply bisim_refl.
Defined.

Lemma constr' : forall (A : Type) (s : stream A),
  s = Build_stream _ s.(hd) s.(tl).
Proof.
  intros. 
  Fail destruct s. 
Abort.

Eval compute in constr _ ticks.

Notation convertible x y := (eq_refl x : x = y).

Fail Check convertible ticks {| hd := hd ticks; tl := tl ticks |}.

CoInductive U := inU
 { outU : U }.

CoFixpoint u : U :=
  inU u.

CoFixpoint force (u : U) : U :=
  inU (outU u).

Lemma eq (x : U) : x = force x.
Proof.
  Fail destruct x.
Abort.
  (* Impossible *)