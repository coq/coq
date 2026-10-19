(* Print Assumptions reuses traversals across queries in one environment.
   Closing a section discharges its constants under the same names, so
   nothing traversed inside the section may be replayed outside it. A
   section variable's type is not traversed, even when it names an axiom. *)

Axiom ax : nat.
Axiom T : Type.
Axiom t0 : T.

Section S.
  Variable a : nat.
  Variable v : (fun _ : T => nat) t0.
  Let l : nat := ax.
  Definition g := a.
  Definition h := v + l.
  Definition k := h.
  Print Assumptions g.
  Print Assumptions g.
  Print Assumptions k.
  Print Assumptions h.
End S.

Print Assumptions g.
Print Assumptions g.
Print Assumptions k.
Print Assumptions h.
