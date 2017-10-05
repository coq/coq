(* testing info/debug auto/eauto *)

Goal False \/ (True -> True).
info_auto.
Undo.
debug auto.
Undo.
info_eauto.
Undo.
debug eauto.
Qed.

Goal True.
info_trivial.
Qed.
