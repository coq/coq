From Stdlib Require Import FSetAVL.
Declare Module NatKey : OrderedType.OrderedType
    with Definition t := nat
    with Definition eq := @ eq nat.
#[local] Remove Hints NatKey.eq_trans NatKey.eq_refl.
Module Import NatMap := FSetAVL.Make NatKey.
Goal forall x y, NatMap.E.eq x y.
  Timeout 1 intros; debug eauto.
Admitted.
