Goal (fun A (P Q : A -> Prop) (X : sigT2 P Q) => proj1_sig X) = (fun A (P Q : A -> Prop) (X : sigT2 P Q) => projT1 X).
  reflexivity.
Qed.

Goal (fun A (P Q : A -> Prop) (X : sigT2 P Q) => proj2_sig X) = (fun A (P Q : A -> Prop) (X : sigT2 P Q) => projT2 X).
  reflexivity.
Qed.

Goal (fun A (P Q : A -> Prop) (X : sigT2 P Q) => proj3_sig X) = (fun A (P Q : A -> Prop) (X : sigT2 P Q) => projT3 X).
  reflexivity.
Qed.
