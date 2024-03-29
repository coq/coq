Module A.
  Set Primitive Projections.
  Record hSet : Type := BuildhSet { setT : Type;  iss : True }.
  Ltac head_hnf_under_binders x :=
  match eval hnf in x with
    | ?f _ => head_hnf_under_binders f
    | (fun y => ?f y) => head_hnf_under_binders f
    | ?y => y
  end.
Goal forall s : hSet, True.
intros.
let x := head_hnf_under_binders setT in pose x.

set (foo := eq_refl (@setT )). generalize foo. simpl. cbn.
Abort.
End A.

Module A'.
Set Universe Polymorphism.
 Set Primitive Projections.
Record hSet (A : Type) : Type := BuildhSet { setT : Type;  iss : True }.
Ltac head_hnf_under_binders x :=
  match eval compute in x with
    | ?f _ => head_hnf_under_binders f
    | (fun y => ?f y) => head_hnf_under_binders f
    | ?y => y
  end.
Goal forall s : @hSet nat, True.
intros.
let x := head_hnf_under_binders setT in pose x.

set (foo := eq_refl (@setT nat)). generalize foo. simpl. cbn.
Abort.
End A'.
