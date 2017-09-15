Module M.
  Inductive I : Set := C : nat -> I.
End M.

Module M1 := M.


Goal forall x, M.C x = M1.C 0 -> x = 0 .
  intros x H.
  (*
     injection sur deux constructeurs egaux mais appeles
     par des modules differents
     *)
  injection H.
  tauto.
Qed.

Goal  M.C 0 <> M1.C 1.
  (*
     Discriminate sur deux constructeurs egaux mais appeles
     par des modules differents
     *)
  intro H;discriminate H.
Qed.


Goal forall x,  M.C x = M1.C 0 -> x = 0.
  intros x H.
  (*
     inversion sur deux constructeurs egaux mais appeles
     par des modules differents
     *)
  inversion H. reflexivity.
Qed.
