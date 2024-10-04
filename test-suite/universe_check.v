Set Universe Polymorphism.
(* So that by default we only get Set <= a constraints, not Set < a *)
Set Printing Universes.

Section test_loop.
  Universes a b c d.
  Constraint b < a.
  Constraint c <= d.
  Fail Constraint d < c.
End test_loop.

Section funext.
  Universes a b c d.

  Constraint Set < a.
  Constraint b < a.
  Constraint Set < c.
  Constraint c < b.
  Constraint d <= a.

  Check Constraint d <= a.
End funext.

Section test_loop.
  Universes a b.
  Constraint a < b.
  Fail Check Constraint b < a.
  Fail Constraint b < a.
End test_loop.

Section test.
Universes a b c d.

Constraint a < b.
Constraint b < c.
Constraint c < d.

Check Constraint Set < b.

End test.

Section test2.
  Universes a b.
  Constraint a <= b.
  Fail Check Constraint a = b.

  Constraint b <= a.
  Check Constraint a = b.
End test2.

Section test3.
  Universes a b c d.
  Constraint a <= c.
  Constraint b <= c.
  Fail Check Constraint a <= b.
  Check Constraint a <= c.
  Constraint a <= d, d <= b.
  Check Constraint a <= b.

  Constraint b <= a.
  Check Constraint a = b, a = d.
End test3.

Section incr.
  Universe a b c.

  Constraint a <= b + 1.
  Constraint b + 1 <= a.
  Check Constraint b <= a.

  Check Constraint a + 2 = b + 3.

End incr.

Section maximpl.
  Universe a b c.

  Constraint a <= max (b, c).
  Fail Check Constraint a <= b.
  Fail Check Constraint a <= c.
  Check Constraint a <= max (b, c).

  (* If we add this constraint, then max (b, c) = c and a <= c holds *)
  Constraint b <= c.
  Fail Check Constraint a <= b.
  Check Constraint a <= c.

  Check Constraint max (b, c) = c.

End maximpl.

Section merge_noincr.
  Universe a b c.

  Constraint a <= b.
  Constraint b <= c. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  Constraint c <= a. (* Now c + 1 <= a <= c + 1 *)
  Check Constraint c = a.
End merge_noincr.

Section merge_incr.
  Universe a b c.

  Constraint a <= b + 1.
  Constraint b + 1 <= c. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  Constraint c <= a.
  (* Now c = a = b + 1 *)
  Check Constraint c = a, c = b + 1.
End merge_incr.


Section merge_incr_trans.
  Universe a b c.

  Constraint a <= b + 1.
  Constraint b + 1 <= c + 2. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  Fail Constraint c + 3 <= a.
  Constraint c + 2 <= a.
  (* Now c = a = b + 1 *)
  Check Constraint c + 2 = a, c + 1 = b. (* as c + 2 = b + 1, c + 1 = b *)

End merge_incr_trans.

Section merge_incr_all_incr.
  Universe a b c.

  Constraint a + 2 <= b + 1.
  Constraint b + 1 <= c + 6. (* implies b + 2 <= c + 1, so a <= c + 1 *)

  (* Constraint c + 3 <= a + 2.   *)
  Constraint c + 6 <= a + 2.
  (* Now c = a = b + 1 *)
  Check Constraint c + 6 = a + 2, c + 5 = b. (* as c + 2 = b + 1, c + 1 = b *)

End merge_incr_all_incr.

Module PrivatePoly.
  Set Private Polymorphic Universes.
  Set Universe Polymorphism.

  Set Debug "loop-checking-find-to-merge".
  Set Debug "loop-checking-global".


  Lemma foo@{i} : Type@{i}.
  Proof. exact Type. Qed.

  Check foo@{_}.

  Unset Private Polymorphic Universes.

  Lemma bar : Type. Proof. exact Type. Qed.
  Check bar@{_ _}.

  Set Private Polymorphic Universes.
  Unset Strict Universe Declaration.

  Lemma baz : Type@{outer}. Proof. exact Type@{inner}. Qed.
  About baz.
End PrivatePoly.

Set Debug "loop-checking-find-to-merge".
Set Debug "loop-checking-global".

Polymorphic Definition type@{u} := Type@{u}.
Fail Check type@{Prop}.

Polymorphic Definition sort@{s | u |} := Type@{s|u}.
Eval cbv in sort@{Prop|Set}.
Eval cbv in sort@{Type|Set}.

Module max_union_find.
  (* Test that the union-find works through max() constraints *)
  Unset Universe Polymorphism.

  Universes u x y.

  Constraint x <= u.
  Constraint y <= u.
  Constraint u <= max(x, y).

  Fail Check Constraint u = x.
  Fail Check Constraint u = y.
  Set Debug "loop-checking-find-to-merge-global".
  Constraint x <= y.
  Fail Check Constraint u = x.
  Check Constraint u = y.
End max_union_find.

Module max_union_find2.
  (* Test that the union-find works through max() constraints *)
  Unset Universe Polymorphism.

  Universes x y z w.
  Constraint y <= w, z <= w, w <= x.
  Fail Check Constraint x <= max(y, z).

  Constraint x <= max(y, z).
  Check Constraint x = w.
  Fail Check Constraint x = z.
  Fail Check Constraint x = y.
  Constraint w <= y.
  Check Constraint x = y.
  Fail Check Constraint x = z.
  Constraint w <= z.
  Check Constraint x = z.

End max_union_find2.

Module max_union_find3.
  (* Test that the union-find works through max() constraints *)
  Unset Universe Polymorphism.

  Universes x y z w.
  Constraint y <= w, z <= w, w <= x.
  Fail Check Constraint x <= max(y, z).
  Constraint w <= y.
  Constraint w <= z.
  Fail Check Constraint x = z.
  Fail Check Constraint x = y.
  Constraint x <= max(y, z).
  Check Constraint x = w.
  Check Constraint x = z.
  Check Constraint x = y.
End max_union_find3.

Module max_union_find4.
  (* Test that the union-find works through max() constraints *)
  Unset Universe Polymorphism.

  Universes x y z w x'.
  Constraint y <= w, z <= w, w <= x, x <= x'.
  Fail Check Constraint x <= max(y, z).
  Constraint w <= y.
  Constraint w <= z.
  Fail Check Constraint x = z.
  Fail Check Constraint x = y.
  Fail Check Constraint x = x'.
  Check Constraint w = y.
  Check Constraint w = z.
  (* Set Debug "loop-checking-enforce-eq". *)
  Set Debug "loop-checking".
  Constraint x' <= max(y, z).
  Check Constraint x = w.
  Check Constraint x = z.
  Check Constraint x = y.
  Check Constraint x = x'.
End max_union_find4.
