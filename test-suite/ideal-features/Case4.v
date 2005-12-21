Inductive listn : nat -> Set :=
  | niln : listn 0
  | consn : forall n : nat, nat -> listn n -> listn (S n).

Inductive empty : forall n : nat, listn n -> Prop :=
    intro_empty : empty 0 niln.

Parameter
  inv_empty : forall (n a : nat) (l : listn n), ~ empty (S n) (consn n a l).

Type
  (fun (n : nat) (l : listn n) =>
   match l in (listn n) return (empty n l \/ ~ empty n l) with
   | niln => or_introl (~ empty 0 niln) intro_empty
   | consn n O y as b => or_intror (empty (S n) b) (inv_empty n 0 y)
   | consn n a y as b => or_intror (empty (S n) b) (inv_empty n a y)
   end).


Type
  (fun (n : nat) (l : listn n) =>
   match l in (listn n) return (empty n l \/ ~ empty n l) with
   | niln => or_introl (~ empty 0 niln) intro_empty
   | consn n O y => or_intror (empty (S n) (consn n 0 y)) (inv_empty n 0 y)
   | consn n a y => or_intror (empty (S n) (consn n a y)) (inv_empty n a y)
   end).

Type
  (fun (n : nat) (l : listn n) =>
   match l in (listn n) return (empty n l \/ ~ empty n l) with
   | niln => or_introl (~ empty 0 niln) intro_empty
   | consn O a y as b => or_intror (empty 1 b) (inv_empty 0 a y)
   | consn n a y as b => or_intror (empty (S n) b) (inv_empty n a y)
   end).
