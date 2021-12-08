Definition my_fun (n:nat) := n.

Section My_Sec.
  Global Arguments my_fun x : rename.
End My_Sec.

(* The following code suffices to trigger it, on my system:

    Definition my_fun (n:nat) := n.

    Section My_Sec.
    Global Arguments my_fun x : rename.
    End My_Sec.

The `Global Arguments` declaration succeeds fine, but the `End My_Sec` fails, with `Anomaly: dirpath_prefix: empty dirpath. Please report.`

If `Global` is removed, or if no arguments are renamed, then everything works as expected.

If other declarations go between the `Global Arguments` and the `End My_Sec`, then the other declarations work normally, but the `End My_Sec` still fails.

Previously reported at https://github.com/HoTT/coq/issues/24 .  Occurs in both 8.4 and current trunk. *)
