Require Import Ltac2.Ltac2.
Import Printf.
Set Default Proof Mode "Classic".

(* [Force] is normally used to turn an evar that is not eligible for typeclass
   search into a (new) one that is eligible. *)
Definition Force {T : Type} (_ : T) : Type := T.
Hint Opaque Force : main.
Existing Class Force.

(* We create a new evar that is deemed eligible for TC search and unify that
   with the existing evar. *)
Hint Extern 0 (@Force ?T ?l) =>
  assert_succeeds (idtac; is_evar l);
  let f :=
    ltac2:(x y |-
      let x := Option.get (Ltac1.to_constr x) in
      let y := Option.get (Ltac1.to_constr y) in
      printf "before";
      printf "x = %t" x;
      printf "y = %t" y;
      Unification.unify TransparentState.empty x y;
      printf "after";
      printf "x = %t" x;
      printf "y = %t" y
    )
  in
  (unshelve
    let n := open_constr:(?[n] :> T) in
    notypeclasses refine n);
  f l ?n
: main.

(* A dummy class so that we have something to force. *)
Class Foo  (P : Prop) := {}.
(* We make searches for [Foo] fail in malformed contexts by calling [cbn] on all hypotheses. *)
Hint Extern 0 (Foo _) => cbn in *; constructor : main.

(* A definition that has more data than its body *)
Definition Bar : forall {T}, T -> Type := fun _ _ => True.
(* A "constructor" for [Bar] *)
Definition mk : forall {T} (t : T), Bar t := fun _ _ => I.

Goal True.
Proof.
  Set Printing Existential Instances.
  (* We create two evars
     1. ?x : [|- Foo False]
     2. ?p : [a : unit; H := mk a : Bar a |- Force ?x]
   *)
  let x := open_constr:(?[x] :> Foo False) in
  pose proof (a := tt);
  pose (H := mk a);
  unshelve epose proof (?[p] : Force x).
  (* Creating a fresh evar ?n (in the bigger context) and unifying it with ?x
  (no context) works fine. It is simply equated with ?x, i.e. the extended
  context is no longer available to it. Just as expected.. *)
  Succeed typeclasses eauto with main.
  (*
    before
    x = ?x
    y = ?n@{a:=a; H:=H}
    after
    x = ?x
    y = ?x
  *)
  (* If we reduce [mk a] in H, unification goes terribly wrong: The fresh evar
     has its context restricted to [H := I : Bar a]. Note that [a] is a dangling
     reference. It is absent from the context.
   *)
  change (mk a) with I in H.
  typeclasses eauto with main.
  (*
    before
    x = ?x
    y = ?n@{a:=a; H:=H}
    after
    x = ?n@{H:=I}
    y = ?n@{H:=H}
  *)
Abort.
