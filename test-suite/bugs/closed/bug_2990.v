Goal True.
Proof.
  evar (pfT : Type).
  cut pfT.
  subst pfT.
  intro pf.
  refine ((fun A : Set => pf A) unit).
Abort.
