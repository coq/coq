Require Import TestSuite.admit.
Module ETassi.
  Axiom admit : forall {T}, T.
  Class IsHProp (A : Type) : Type := {}.
  Class IsHSet (A : Type) : Type := {}.
  Record hProp := hp { hproptype :> Type ; isp : IsHProp hproptype}.
  Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
  Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
  Global Instance isset_hProp : IsHSet hProp | 0.

  Check (eq_refl _ : setT (default_HSet _ _) = hProp).
  Check (eq_refl _ : setT _ = hProp).
End ETassi.

Module JGross.
  (* File reduced by coq-bug-finder from original input, then from 6462 lines to 5760 lines, then from 5761 lines to 181 lines, then from 191 lines to 181 lines, then from 181 lines to 83 lines, then from 87 lines to 27 lines *)
  Axiom admit : forall {T}, T.
  Class IsHProp (A : Type) : Type := {}.
  Class IsHSet (A : Type) : Type := {}.
  Inductive Unit : Set := tt.
  Record hProp := hp { hproptype :> Type ; isp : IsHProp hproptype}.
  Definition Unit_hp:hProp:=(hp Unit admit).
  Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
  Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
  Global Instance isset_hProp : IsHSet hProp | 0.
  Definition isepi {X Y} `(f:X->Y) := forall Z: hSet,
                                      forall g h: Y -> Z, (fun x => g (f x)) = (fun x => h (f x)) -> g = h.
  Lemma isepi_issurj {X Y} (f:X->Y): isepi f -> True.
  Proof.
    intros epif.
    set (g :=fun _:Y => Unit_hp).
    pose proof (epif (default_HSet hProp isset_hProp) g).
    specialize (epif _ g).
    (* Toplevel input, characters 34-35:
Error:
In environment
X : Type
Y : Type
f : X -> Y
epif : isepi f
g := fun _ : Y => Unit_hp : Y -> hProp
H : forall h : Y -> default_HSet hProp isset_hProp,
    (fun x : X => g (f x)) = (fun x : X => h (f x)) -> g = h
The term "g" has type "Y -> hProp" while it is expected to have type
 "Y -> ?30".
     *)
  Abort.
End JGross.
