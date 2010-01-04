(* Test pattern with dependent occurrences; Note that it does not
   behave as the succession of three generalize because each
   quantification introduces new occurrences that are automatically
   abstracted with the numbering still based on the original statement *)

Goal (id true,id false)=(id true,id true).
generalize bool at 2 4 6 8 10 as B, true at 3 as tt, false as ff.
Abort.

(* Check use of occurrences in hypotheses for a reduction tactic such
   as pattern *)

(* Did not work in 8.2 *)
Goal 0=0->True.
intro H.
pattern 0 in H at 2.
set (f n := 0 = n) in H.  (* check pattern worked correctly *)
Abort.

(* Syntactic variant which was working in 8.2 *)
Goal 0=0->True.
intro H.
pattern 0 at 2 in H.
set (f n := 0 = n) in H.  (* check pattern worked correctly *)
Abort.

(* Ambiguous occurrence selection *)
Goal 0=0->True.
intro H.
pattern 0 at 1 in H at 2 || exact I.  (* check pattern fails *)
Qed.

(* Ambiguous occurrence selection *)
Goal 0=1->True.
intro H.
pattern 0, 1 in H at 1 2 || exact I.  (* check pattern fails *)
Qed.

(* Occurrence selection shared over hypotheses is difficult to advocate and
   hence no longer allowed *)
Goal 0=1->1=0->True.
intros H1 H2.
pattern 0 at 1, 1 in H1, H2 || exact I.  (* check pattern fails *)
Qed.

(* Test catching of reduction tactics errors (was not the case in 8.2) *)
Goal eq_refl 0 = eq_refl 0.
pattern 0 at 1 || reflexivity.
Qed.
