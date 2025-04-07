Set Printing All.
(* Set Typeclasses Debug Verbosity 2. *)

Create HintDb test discriminated.

Definition id {X} (x:X) := x.

Hint Transparent id : test.

Definition opq {X} (x:X) := x.

Hint Opaque opq : test.

Definition const {X} (x y : X) := x.

Hint Transparent const : test.

Class C {X:Type} (x : X) := MKC {}.

Module M1.
  Definition f1 (_ : unit) := tt.
  Hint Opaque f1 : test.

  Definition C1 : C (fun x => f1 x) := MKC _ _.
  Hint Resolve C1 : test.

  Goal C (fun x => f1 x).
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Qed.

  Goal C (fun x => id (f1) x).
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Qed.

  Goal C (fun x => opq (f1) x).
  Proof.
    Print HintDb test.
    Fail typeclasses eauto with test.
  Abort.

  Goal C f1.
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Qed.
End M1.


Module M2.
  Definition f2 (_ _ : unit) := tt.
  Hint Opaque f2 : test.

  Definition C2 : C (fun x y : unit => f2 x y) := MKC _ _.
  Hint Resolve C2 : test.

  Goal C (fun x y : unit => f2 x y).
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Abort.

  Goal C (fun x y : unit => id f2 x y).
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Abort.

  Goal C f2.
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Abort.

  Definition C2f : C (fun z x y : unit => f2 x y) := MKC _ _.
  Hint Resolve C2f : test.

  Goal C (fun z : unit => f2).
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Abort.

End M2.

Module const.
  Inductive option (X : Type) := None | Some (x : X).
  Definition C_constant {X Y} (c : Y) : C (fun _ : X => c) := MKC _ _.
  Hint Resolve C_constant : test.

  Goal C (fun _ : nat => @None unit).
  Proof.
    Print HintDb test.
    typeclasses eauto with test.
  Qed.

End const.

Module PrimProjParamsNoArgs.
  #[projections(primitive)]
  Record r (dummy : unit) := v { f : unit }.
  Hint Opaque f : test.

  (* Proj hint, Proj goal *)
  Module M1.
    Definition C_pproj dummy : C (fun r : r dummy => r.(f _)) := MKC _ _.
    Hint Resolve C_pproj : test.

    Goal forall dummy, C (fun r : r dummy => r.(f _)).
    Proof.
      intros dummy.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M1.

  (* Proj hint, Compat constant goal *)
  Module M2.
    Definition C_pproj (dummy : unit) : C (fun r => f dummy r) := MKC _ _.
    Hint Resolve C_pproj : test.

    Goal forall dummy, C (fun r : r dummy => ltac:(exact (f dummy)) r).
    Proof.
      intros dummy.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M2.

  (* Compat constant hint, Proj goal *)
  Module M3.
    Definition C_pproj (dummy : unit) : C (fun r => ltac:(exact (f dummy)) r) := MKC _ _.
    Hint Resolve C_pproj : test.

    Goal forall dummy, C (fun r : r dummy => r.(f _ )).
    Proof.
      intros dummy.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M3.

  (* Compat constant hint, compat constant goal *)
  Module M4.
    Definition C_pproj (dummy : unit) : C (fun r => ltac:(exact (f dummy)) r) := MKC _ _.
    Hint Resolve C_pproj : test.

    Goal forall dummy, C (fun r => ltac:(exact (f dummy)) r).
    Proof.
      intros dummy.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M4.
End PrimProjParamsNoArgs.

Module PrimProjParamsArgs.
  #[projections(primitive)]
  Record r (dummy : unit) := v { f : nat }.
  Hint Opaque f : test.

  Axiom (P : (unit -> unit -> unit -> nat) -> Prop).

  Axiom (x : r tt).

  (* Proj hint, Proj goal *)
  Module M1.
    Definition C_pproj : C (P (fun _ _ _ : unit => x.(f _))) := MKC _ _.
    Hint Resolve C_pproj : test.
    Goal C (P (fun _ _ _ : unit => x.(f _))).
    Proof.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M1.

  (* Proj hint, Compat constant goal *)
  Module M2.
    Definition C_pproj : C (P (fun _ _ _ : unit => x.(f _))) := MKC _ _.
    Hint Resolve C_pproj : test.
    Goal C (P (fun _ _ _ : unit => ltac:(exact (f _ x)))).
    Proof.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M2.

  (* Compat constant hint, Proj goal *)
  Module M3.
    Definition C_pproj : C (P (fun _ _ _ : unit => ltac:(exact (f _ x)))) := MKC _ _.
    Hint Resolve C_pproj : test.
    Goal C (P (fun _ _ _ : unit => x.(f _))).
    Proof.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M3.

  (* Compat constant hint, compat constant goal *)
  Module M4.
    Definition C_pproj : C (P (fun _ _ _ : unit => ltac:(exact (f _ x)))) := MKC _ _.
    Hint Resolve C_pproj : test.
    Goal C (P (fun _ _ _ : unit => ltac:(exact (f _ x)))).
    Proof.
      Print HintDb test.
      typeclasses eauto with test.
    Qed.
  End M4.
End PrimProjParamsArgs.

Module Negative.
  (* To test the discriminating power of the bnet we construct a hint that
     always succeeds. Then, we manually restrict it to interesting patterns and
     ensure that the application is never attempted by asserting that the
     overall search fails. *)

  Definition CA {X} x : @C X x := MKC _ _.


  Definition f (_ _ : unit) := tt.
  Definition g (_ _ : unit) := tt.
  Hint Opaque f g : test.

  Module M1.
    Hint Resolve CA | (@C _ (fun x => f x)) : test.

    Goal C (fun x => g x).
    Proof.
      Fail typeclasses eauto with test.
    Abort.
  End M1.

  Module M1i.
    Hint Resolve CA | (@C _ (fun x => f (id x))) : test.

    Goal C (fun x => g x).
    Proof.
      Fail typeclasses eauto with test.
    Abort.
  End M1i.

  Module M1o.
    Hint Resolve CA | (@C _ (fun x => f (opq x))) : test.

    Goal C (fun x => g x).
    Proof.
      Fail typeclasses eauto with test.
    Abort.
  End M1o.
End Negative.
