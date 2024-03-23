
Set Warnings "+failed-abstract-certificate".
Goal True.
Proof.
  do 2 assert True by abstract (pose proof Type;exact I).
  exact I.
Qed.
