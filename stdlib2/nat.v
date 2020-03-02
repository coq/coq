Require Import prelude ssreflect datatypes decimal.
Import equality prop.

Inductive nat :=
| O
| S of nat.

Register nat as num.nat.type.
Register O as num.nat.O.
Register S as num.nat.S.

Declare Scope nat_scope.
Delimit Scope nat_scope with N.
Local Open Scope nat_scope.
Bind Scope nat_scope with nat.
Arguments S _%nat_scope.

Notation succn := S.

Definition predn (n: nat) : nat :=
  if n is succn n' then n' else n.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.

Lemma natI (m n: nat) :
  m = n ->
  if m is m'.+1 then if n is n'.+1 then m' = n' else False
  else if n is O then True else False.
Proof. by move => ->; case: n. Qed.

Fixpoint tail_add (m n: nat) : nat :=
  if m is S m' then tail_add m' (S n) else n.

Fixpoint tail_addmul (r m n: nat) : nat :=
  if m is S m' then tail_addmul (tail_add n r) m' n else r.

Definition tail_mul n m := tail_addmul O n m.

(** ** Conversion with a decimal representation for printing/parsing *)

Local Notation ten := (S (S (S (S (S (S (S (S (S (S O)))))))))).

Fixpoint of_uint_acc (d: uint) (acc: nat) :=
  match d with
  | Nil => acc
  | D0 d => of_uint_acc d (tail_mul ten acc)
  | D1 d => of_uint_acc d (S (tail_mul ten acc))
  | D2 d => of_uint_acc d (S (S (tail_mul ten acc)))
  | D3 d => of_uint_acc d (S (S (S (tail_mul ten acc))))
  | D4 d => of_uint_acc d (S (S (S (S (tail_mul ten acc)))))
  | D5 d => of_uint_acc d (S (S (S (S (S (tail_mul ten acc))))))
  | D6 d => of_uint_acc d (S (S (S (S (S (S (tail_mul ten acc)))))))
  | D7 d => of_uint_acc d (S (S (S (S (S (S (S (tail_mul ten acc))))))))
  | D8 d => of_uint_acc d (S (S (S (S (S (S (S (S (tail_mul ten acc)))))))))
  | D9 d => of_uint_acc d (S (S (S (S (S (S (S (S (S (tail_mul ten acc))))))))))
  end.

Definition of_uint (d: uint) := of_uint_acc d O.

Definition to_little_uint (n: nat) (acc: uint) : uint :=
  nat_rect acc (λ _, Little.succ) n.

Definition to_uint (n: nat) : uint :=
  decimal.rev (to_little_uint n decimal.zero).

Numeral Notation nat of_uint to_uint : nat_scope.
