Require Export ZArith.
Require Export ZArithRing.

Tactic Definition compute_POS :=
 (Match Context With
 | [|- [(POS (xI ?1))]] -> Let v = ?1 In 
                          (Match v With
                            | [xH] ->
                              (Fail 1)
                            |_->
                              Rewrite (POS_xI v))
 | [ |- [(POS (xO ?1))]] -> Let v = ?1 In
                           Match v With
                            |[xH]->
                              (Fail 1)
                            |[?]->
                              Rewrite (POS_xO v)).

Goal (x:positive)(POS (xI (xI x)))=`4*(POS x)+3`.
Intros.
Repeat compute_POS.
Ring.
Qed.
