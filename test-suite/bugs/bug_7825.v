Record T (x : nat) := { t : x = x }.

Goal exists x, T x.
  refine (ex_intro _ _ _).
  Show Existentials.
  simple refine {| t := _ |}.
  reflexivity.
  Unshelve. exact 0.
Qed.

(** Fine if the new evar is defined as the originally shelved evar:  we do nothing.
  In the other direction we promote the non-shelved new goal to a shelved one:
  shelved status has priority over goal status. *)

Goal forall a : nat,  exists x, T x.
   evar (x : nat). subst x. Show Existentials.
   intros a. simple refine (ex_intro ?[x0] _ _). shelve. simpl.
   (** Here ?x := ?x0 which is shelved, so ?x becomes shelved even if it would
   not be by default (refine ?x and _ produce non-shelved evars by default)*)
   simple refine (Build_T ?x _).
   reflexivity.
   Unshelve. exact 0.
Qed.

Goal { A : _ & { P : _ & @sigT A P } }.
  epose _ as A;
  epose _ as P;
  exists A, P.
  (* Regardless of which evars are in the goals vs the hypotheses,
     [simple refine (existT _ _ _)] should leave over two goals.  This
     should be true even when chained with epose. *)
  assert_succeeds (simple refine (existT _ _ _); let n := numgoals in guard n = 2);
  subst P;
  assert_succeeds (simple refine (existT _ _ _); let n := numgoals in guard n = 2);
  subst A;
  assert_succeeds (simple refine (existT _ _ _); let n := numgoals in guard n = 2).
  (* fails *)
Abort.

Goal { A : _ & { P : _ & @sigT A P } }.
  epose _ as A;
  epose _ as P;
  exists A, P; (* In this example we chain everything *)
  assert_succeeds (simple refine (existT _ _ _); let n := numgoals in guard n = 2);
  subst P;
  assert_succeeds (simple refine (existT _ _ _); let n := numgoals in guard n = 2);
  subst A;
  assert_succeeds (simple refine (existT _ _ _); let n := numgoals in guard n = 2).
  (* fails *)
Abort.
