Goal True.
Fail timeout 2 ((timeout 1 repeat cut True) || (repeat cut True)).
Fail Timeout 2 ((timeout 1 repeat cut True) || (repeat cut True)).
Fail timeout 1 ((timeout 2 repeat cut True) || idtac "fail").
auto.
Qed.
