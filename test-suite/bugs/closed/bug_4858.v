Require Import Nsatz.
Goal True.
try nsatz_compute
 (PEc 0%Z :: PEc (-1)%Z
    :: PEpow (PEsub (PEX Z 2) (PEX Z 3)) 1
       :: PEsub (PEX Z 1) (PEX Z 1) :: nil).
Abort.
