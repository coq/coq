Set Implicit Arguments.

Theorem eq_rect_eq_dec :
  forall A:Type,
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (p:A) (Q:A -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Admitted.

Module Nat.
Include Init.Nat.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Admitted.
Theorem add_comm : forall n m, n + m = m + n.
Admitted.

End Nat.

Notation eq_nat_dec := Nat.eq_dec (only parsing).

Theorem eq_rect_nat_double : forall T (a b c : nat) x ab bc,
  eq_rect b T (eq_rect a T x b ab) c bc = eq_rect a T x c (eq_trans ab bc).
Admitted.

Ltac eq_rect_simpl :=
  unfold eq_rec_r, eq_rec;
  repeat rewrite eq_rect_nat_double;
  repeat rewrite <- (eq_rect_eq_dec eq_nat_dec).

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall n, word n -> word (S n).
Fixpoint natToWord (sz n : nat) : word sz.
Admitted.

Definition wzero sz := natToWord sz 0.
Definition wtl sz (w : word (S sz)) : word sz.
Admitted.

Fixpoint combine (sz1 : nat) (w : word sz1) : forall sz2, word sz2 -> word (sz1 + sz2) :=
  match w in word sz1 return forall sz2, word sz2 -> word (sz1 + sz2) with
    | WO => fun _ w' => w'
    | WS b w' => fun _ w'' => WS b (combine w' w'')
  end.
Fixpoint split2 (sz1 sz2 : nat) : word (sz1 + sz2) -> word sz2.
exact (match sz1 with
    | O => fun w => w
    | S sz1' => fun w => split2 sz1' sz2 (wtl w)
  end).
Defined.

Definition wrshift (sz : nat) (w : word sz) (n : nat) : word sz.
  refine (split2 n sz _).
  rewrite Nat.add_comm.
  exact (combine w (wzero n)).
Defined.

Theorem combine_n_0 : forall sz1 (w : word sz1) (v : word 0),
  combine w v = eq_rect _ word w _ (plus_n_O sz1).
Admitted.

Theorem wrshift_0 : forall sz (w : word sz), @wrshift sz w 0 = w.
Proof.
  intros.
  unfold wrshift.
  simpl.
  rewrite combine_n_0.
  eq_rect_simpl.
  reflexivity.
Qed.
