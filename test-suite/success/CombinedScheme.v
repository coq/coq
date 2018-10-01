Inductive even (x : bool) : nat -> Type :=
| evenO : even x 0
| evenS : forall n, odd x n -> even x (S n)
with odd (x : bool) : nat -> Type :=
| oddS : forall n, even x n -> odd x (S n).

Scheme even_ind_prop := Induction for even Sort Prop
with odd_ind_prop := Induction for odd Sort Prop.

Combined Scheme even_cprop from even_ind_prop, odd_ind_prop.

Check even_cprop :
  forall (x : bool) (P : forall n : nat, even x n -> Prop)
    (P0 : forall n : nat, odd x n -> Prop),
    P 0 (evenO x) ->
    (forall (n : nat) (o : odd x n), P0 n o -> P (S n) (evenS x n o)) ->
    (forall (n : nat) (e : even x n), P n e -> P0 (S n) (oddS x n e)) ->
    (forall (n : nat) (e : even x n), P n e) /\
    (forall (n : nat) (o : odd x n), P0 n o).

Scheme even_ind_type := Induction for even Sort Type
with odd_ind_type := Induction for odd Sort Type.

(* This didn't work in v8.7 *)

Combined Scheme even_ctype from even_ind_type, odd_ind_type.

Check even_ctype :
  forall (x : bool) (P : forall n : nat, even x n -> Prop)
    (P0 : forall n : nat, odd x n -> Prop),
    P 0 (evenO x) ->
    (forall (n : nat) (o : odd x n), P0 n o -> P (S n) (evenS x n o)) ->
    (forall (n : nat) (e : even x n), P n e -> P0 (S n) (oddS x n e)) ->
    (forall (n : nat) (e : even x n), P n e) *
    (forall (n : nat) (o : odd x n), P0 n o).
