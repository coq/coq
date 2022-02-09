Fixpoint big_opL {A} f (xs : list A) : Prop :=
  match xs with
  | nil => True
  | cons x xs => (f 0 x) /\ (big_opL (fun n => f (S n)) xs)
  end.
Arguments big_opL {_} _ !xs /.
Goal forall A f xs, @big_opL A f xs.
  induction xs; [admit|]; cbn.
  match goal with
    |- _ /\ big_opL _ _ => idtac
  end.
Abort.
(*
  f 0 a /\
  (fix big_opL (A0 : Type) (f0 : nat -> A0 -> Prop) (xs0 : list A0) {struct xs0} : Prop :=
     match xs0 with
     | nil => True
     | x :: xs1 => f0 0 x /\ big_opL A0 (fun n : nat => f0 (S n)) xs1
     end) A (fun n : nat => f (S n)) xs
*)
