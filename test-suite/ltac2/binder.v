Require Import Ltac2.Ltac2.

Ltac2 check () :=
let t := Control.goal () in
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod b t =>
  let na := Constr.Binder.name b in
  let u := Constr.Binder.type b in
  let b := Constr.Binder.make na u in
  let c := Constr.Unsafe.make (Constr.Unsafe.Prod b t) in
  pose (v := $c);
  refine (_ : &v);
  unfold &v
| _ => fail
end.

Goal forall x : nat, x = x.
Proof.
check (); intros; reflexivity.
Qed.

Goal forall x : Type, x = x.
Proof.
check (); intros; reflexivity.
Qed.

Goal forall x : Set, x = x.
Proof.
check (); intros; reflexivity.
Qed.

Inductive True : SProp := I.

Goal forall x : True, True.
Proof.
check (); intros; constructor.
Qed.
