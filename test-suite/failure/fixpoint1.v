Fixpoint PreParadox [u:unit] : False := (PreParadox u).
Definition Paradox := (PreParadox tt).