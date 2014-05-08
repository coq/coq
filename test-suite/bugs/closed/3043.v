Goal (fun A (P : A -> Prop) (X : sigT P) => proj1_sig (sig_of_sigT X)) =
     (fun A (P : A -> Prop) (X : sigT P) => projT1 X).
  reflexivity.
Qed.
