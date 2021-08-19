(* This is one part of wish #5264 *)

Goal forall T1 (P1 : T1 -> Type), sigT P1 -> sigT P1.
  intros T1 P1 H1.
  eexists ?[x].
  destruct H1 as [x1 H1].
  apply H1.
Qed.
