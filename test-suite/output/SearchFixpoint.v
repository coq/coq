(** Test file for #18983 *)

(** We test that [Search] allows the [is:Fixpoint] and [is:CoFixpoint] search
    items while not changing [is:Definition]. *)
Module Foo.
Definition foo := 42.

Fixpoint bar (n : nat) :=
  match n with
  | 0 => 0
  | S n => bar n
  end.

(* Example shamelessly taken from the reference manual. *)
CoInductive Stream := Seq : nat -> Stream -> Stream.
CoFixpoint from (n : nat) := Seq n (from (S n)).
End Foo.

Search is:Fixpoint inside Foo.
Search is:CoFixpoint inside Foo.
Search is:Definition inside Foo.
