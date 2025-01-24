Module Type Empty.
End Empty.

Module Type Param.
  Parameter T : Type.
End Param.

Module M0. End M0.

Module FUNC0 (ARG0 : Empty) : Param.
  Definition T : Type := unit.
End FUNC0.

Module FUNC (ARG : Empty).
  Module K := FUNC0(M0).
End FUNC.

Module ANS := FUNC(M0).

Print Assumptions ANS.K.T.
