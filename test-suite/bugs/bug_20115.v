Module Type PARAM.
Parameter T : Type.
End PARAM.

Module Type NESTED.
  Declare Module KI: PARAM.
End NESTED.

Module Type BUNDLE.
  Declare Module KI: PARAM.
  Declare Module K0: NESTED with Module KI := KI.
End BUNDLE.

Declare Module MyKI : PARAM.
Declare Module MyKO : BUNDLE with Module KI := MyKI.

(** Check that the delta-resolver contains the correct equivalence

    MyKO.K0.KI.T ↦ MyKI.T *)

Goal MyKI.T.
Proof.
match goal with
[ |- MyKO.K0.KI.T ] => idtac
end.
Abort.

Goal MyKO.K0.KI.T.
Proof.
match goal with
[ |- MyKI.T ] => idtac
end.
Abort.
