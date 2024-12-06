Require Import PrimInt63.

Module Type T.
  Parameter eq : int -> int -> bool.
End T.

Module M (S : T).
  Definition do x y := S.eq x y.
End M.

Module N.
  Definition eq := eqb.
End N.

Module P := M N.

Check (eq_refl true <: P.do 0 0 = true).
Check (eq_refl true <<: P.do 0 0 = true).
