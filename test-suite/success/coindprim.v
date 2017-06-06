Require Import Program.

Set Primitive Projections.

CoInductive Stream (A : Type) := mkStream { hd : A; tl : Stream A}.

Arguments mkStream [A] hd tl.
Arguments hd [A] s.
Arguments tl [A] s.

Definition eta {A} (s : Stream A) := {| hd := s.(hd); tl := s.(tl) |}.

CoFixpoint ones := {| hd := 1; tl := ones |}.
CoFixpoint ticks := {| hd := tt; tl := ticks |}.

CoInductive stream_equiv {A} (s : Stream A) (s' : Stream A) : Prop :=
  mkStreamEq { hdeq : s.(hd) = s'.(hd); tleq : stream_equiv s.(tl) s'.(tl) }.
Arguments hdeq {A} {s} {s'}.
Arguments tleq {A} {s} {s'}.

Program CoFixpoint ones_eq : stream_equiv ones ones.(tl) :=
  {| hdeq := eq_refl; tleq := ones_eq |}.

CoFixpoint stream_equiv_refl {A} (s : Stream A) : stream_equiv s s :=
  {| hdeq := eq_refl; tleq := stream_equiv_refl (tl s) |}.

CoFixpoint stream_equiv_sym {A} (s s' : Stream A) (H : stream_equiv s s') : stream_equiv s' s :=
  {| hdeq := eq_sym H.(hdeq); tleq := stream_equiv_sym _ _ H.(tleq) |}.

CoFixpoint stream_equiv_trans {A} {s s' s'' : Stream A}
           (H : stream_equiv s s') (H' : stream_equiv s' s'') : stream_equiv s s'' :=
  {| hdeq := eq_trans H.(hdeq) H'.(hdeq);
     tleq := stream_equiv_trans H.(tleq) H'.(tleq) |}.

Program Definition eta_eq {A} (s : Stream A) : stream_equiv s (eta s):=
  {| hdeq := eq_refl; tleq := stream_equiv_refl (tl (eta s))|}.

Section Parks.
  Variable A : Type.

  Variable R : Stream A -> Stream A -> Prop.
  Hypothesis bisim1 : forall s1 s2:Stream A,
      R s1 s2 -> hd s1 = hd s2.
  Hypothesis bisim2 : forall s1 s2:Stream A,
      R s1 s2 -> R (tl s1) (tl s2).
  CoFixpoint park_ppl :
    forall s1 s2:Stream A, R s1 s2 -> stream_equiv s1 s2 :=
    fun s1 s2 (p : R s1 s2) =>
      mkStreamEq _ _ _ (bisim1 s1 s2 p)
      (park_ppl (tl s1)
                (tl s2)
                (bisim2 s1 s2 p)).
End Parks.

Program CoFixpoint iterate {A} (f : A -> A) (x : A) : Stream A :=
  {| hd := x; tl := iterate f (f x) |}.

Program CoFixpoint map {A B} (f : A -> B) (s : Stream A) : Stream B :=
  {| hd := f s.(hd); tl := map f s.(tl) |}.

Theorem map_iterate A (f : A -> A) (x : A) : stream_equiv (iterate f (f x))
                                                         (map f (iterate f x)).
Proof.
apply park_ppl with
(R:= fun s1 s2 => exists x : A, s1 = iterate f (f x) /\
                        s2 = map f (iterate f x)).
now intros s1 s2 (x0,(->,->)).
intros s1 s2 (x0,(->,->)).
now exists (f x0).
now exists x. 
Qed.

Fail Check (fun A (s : Stream A) => eq_refl : s = eta s).

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
