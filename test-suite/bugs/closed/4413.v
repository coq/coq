Goal exists x, x=1 -> True.
 eexists. intro H.
 pose proof (f_equal (fun k => k) H).
Abort.