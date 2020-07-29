(* begin details *)
Definition foo : nat := 3.
(* end details *)

(* begin details : Foo bar *)
Fixpoint idnat (x : nat) : nat :=
  match x with
  | S x => S (idnat x)
  | 0 => 0
  end.
(* end details *)
