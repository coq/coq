Require Import Ltac2.Ltac2.
Import Printf.

Set Default Proof Mode "Classic".

(* A global transparent definition, made opaque while the evar context is
   created so the assumption below keeps the dependency in its type.  There are
   no local definitions with bodies in this example. *)
Definition D {P : Prop} (_ : P) := unit.
Opaque D.

Ltac2 Type exn ::= [ DependencyWasNotPruned ].

Goal forall (P : Prop) (p1 p2 p : P) (d : D p), True.
Proof.
  intros P p1 p2 p d.
  Set Printing Existential Instances.

  let e := open_constr:(?[e] : nat) in
  let test := ltac2:(e p1 p2 |-
    let e := Option.get (Ltac1.to_constr e) in
    let p1 := Option.get (Ltac1.to_constr p1) in
    let p2 := Option.get (Ltac1.to_constr p2) in
    let rec dest_evar c :=
      match Constr.Unsafe.kind c with
      | Constr.Unsafe.Cast c _ _ => dest_evar c
      | Constr.Unsafe.Evar ev args => (ev, args)
      | _ => Control.throw Assertion_failure
      end
    in
    match dest_evar e with
    | (ev, args) =>
      (* The evar context contains [...; p : P; d : D p].  Build the same
         evar at two instances that differ only in the proof [p].  The [d]
         argument is kept equal on both sides. *)
      let args1 := Array.copy args in
      let args2 := Array.copy args in
      Array.set args1 1 p1;
      Array.set args2 1 p2;
      let x := Constr.Unsafe.make (Constr.Unsafe.Evar ev args1) in
      let y := Constr.Unsafe.make (Constr.Unsafe.Evar ev args2) in
      match Constr.Unsafe.check x with
      | Val _ => ()
      | Err _ => Control.throw Assertion_failure
      end;
      match Constr.Unsafe.check y with
      | Val _ => ()
      | Err _ => Control.throw Assertion_failure
      end;

      Unification.unify TransparentState.full x y;

      (* On origin/master, restricting the evar drops [p], so [x] and [y]
         become syntactically equal.  The new closure through LocalAssum types
         keeps [p], so this check fails even though no local definition with a
         body is involved. *)
      printf "x = %t" x;
      printf "y = %t" y;
      if Constr.equal x y then () else Control.throw DependencyWasNotPruned
    end
  ) in
  test e p1 p2.
Abort.
