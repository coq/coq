From Stdlib Require Import ZArith QArith.
From Stdlib.micromega Require Import RingMicromega EnvRing Tauto.
From Stdlib.micromega Require Import ZMicromega QMicromega.

Declare ML Module "micromega_core_plugin:coq-core.plugins.micromega_core".
Declare ML Module "micromega_plugin:coq-core.plugins.micromega".

Goal True.
Proof.
pose (ff :=
  IMPL
    (EQ
       (A isBool
          {|
            Flhs := PEadd (PEX 1) (PEmul (PEc 2%Q) (PEX 2));
            Fop := OpLe;
            Frhs := PEc 3%Q
          |} tt) (TT isBool)) None
    (IMPL
       (EQ
          (A isBool
             {|
               Flhs := PEadd (PEmul (PEc 2%Q) (PEX 1)) (PEX 2);
               Fop := OpLe;
               Frhs := PEc 3%Q
             |} tt) (TT isBool)) None
       (EQ
          (A isBool
             {| Flhs := PEadd (PEX 1) (PEX 2); Fop := OpLe; Frhs := PEc 2%Q |} tt)
          (TT isBool))) : BFormula (Formula Q) isProp).
let ff' := eval unfold ff in ff in wlra_Q wit0 ff'.
Check eq_refl : wit0 = (PsatzAdd (PsatzIn Q 2)
  (PsatzAdd (PsatzIn Q 1) (PsatzMulE (PsatzC 3%Q) (PsatzIn Q 0))) :: nil)%list.
let ff' := eval unfold ff in ff in wlia wit1 ff'.
Check eq_refl : wit1 = (RatProof (PsatzAdd (PsatzIn Z 2) (PsatzAdd (PsatzIn Z 1)
  (PsatzIn Z 0))) DoneProof :: nil)%list.
let ff' := eval unfold ff in ff in wnia wit4 ff'.
Check eq_refl : wit4 = (RatProof (PsatzAdd (PsatzIn Z 2) (PsatzAdd (PsatzIn Z 1)
  (PsatzIn Z 0))) DoneProof :: nil)%list.
let ff' := eval unfold ff in ff in wnra_Q wit5 ff'.
Check eq_refl : wit5 = (PsatzAdd (PsatzIn Q 2)
  (PsatzAdd (PsatzIn Q 1) (PsatzMulE (PsatzC 3%Q) (PsatzIn Q 0))) :: nil)%list.
Fail let ff' := eval unfold ff in ff in wsos_Q wit6 ff'.
Fail let ff' := eval unfold ff in ff in wsos_Z wit6 ff'.
(* Requires Csdp, not in CI
let ff' := eval unfold ff in ff in wpsatz_Z 3 wit2 ff'.
Check eq_refl : wit2 = (RatProof (PsatzAdd (PsatzC 1)
  (PsatzAdd (PsatzIn Z 2) (PsatzAdd (PsatzIn Z 1) (PsatzIn Z 0)))) DoneProof
  :: nil)%list.
let ff' := eval unfold ff in ff in wpsatz_Q 3 wit3 ff'.
Check eq_refl : wit3 = (PsatzAdd (PsatzIn Q 0)
  (PsatzAdd (PsatzMulE (PsatzIn Q 2) (PsatzC (1 # 2)))
            (PsatzAdd (PsatzMulE (PsatzIn Q 1) (PsatzC (1 # 2)))
                      (PsatzMulE (PsatzIn Q 0) (PsatzC (1 # 2))))) :: nil)%list. *)
Abort.
