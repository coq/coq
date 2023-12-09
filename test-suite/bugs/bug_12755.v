Section A.
Context {a : nat}.
Section B.
Context {b : nat}.
Definition foo (eq1 : a = a) (eq2 : b = b) (c : nat) : c = c := eq_refl.
Global Arguments foo _ {_} {d} : rename.
End B.
End A.
Arguments foo. (* was raising an anomaly *)
Check foo _ (d:=0). (* was wrongly binding d to eq2 *)
Fail Check foo (eq1 := 3) (eq_refl 2) (eq_refl 3) 4. (* was wrongly binding eq1 to b *)
