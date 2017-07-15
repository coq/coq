(* destruct on section variables *)
Section section1.
   Variables P Q : Prop.
   Hypothesis H : P /\ Q.
   Theorem p : P.
     destruct H.
     exact H.
   Qed.
End section1.

Section section3.
   Variables P Q : Prop.
   Hypothesis H : P /\ Q.
   Theorem p' : P.
     rename H into H.
     destruct H.
     exact H.
   Qed.
End section3.
