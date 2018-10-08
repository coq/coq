(* These always worked. *)
Goal prod True True. firstorder. Qed.
Goal True -> @sigT True (fun _ => True). firstorder. Qed.
Goal prod True True. dtauto. Qed.
Goal prod True True. tauto. Qed.

(* These should work. *)
Goal @sigT True (fun _ => True). dtauto. Qed.
(* These should work, but don't *)
(* Goal @sigT True (fun _ => True). firstorder. Qed. *)
(* Goal @sigT True (fun _ => True). tauto. Qed. *)
