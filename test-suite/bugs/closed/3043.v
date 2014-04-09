Goal (fun A (P : A -> Prop) (X : sigT P) => proj1_sig X) = 
     (fun A (P : A -> Prop) (X : sigT P) => projT1 X).
  reflexivity.
Qed.
