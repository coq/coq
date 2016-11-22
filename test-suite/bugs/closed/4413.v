(* Regression wrt v8.4 related to the change of order of resolution of evar-evar unification problems. *)

Goal exists x, x=1 -> True.
eexists. intro H.
pose proof (f_equal (fun k => k) H).
Undo.
pose (@f_equal _ _ S _ _ H).
Abort.
