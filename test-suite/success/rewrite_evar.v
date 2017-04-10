Require Import Coq.Setoids.Setoid.

Goal forall (T2 MT1 MT2 : Type) (x : T2) (M2 m2 : MT2) (M1 m1 : MT1) (F : T2 -> MT1 -> MT2 -> Prop),
    (forall (defaultB : T2) (m3 : MT1) (m4 : MT2), F defaultB m3 m4 <-> True) -> F x M1 M2 -> F x m1 m2.
  intros ????????? H' H.
  rewrite (H' _) in *.
  (** The above rewrite should also rewrite in H. *)
  Fail progress rewrite H' in H.
