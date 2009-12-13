Require Import List Program.Syntax.

Variable A:Type.
Variable le:A->A->Prop.
Infix "<=" := le.

(*
if of_sumbool H then _ else _
if H then _ else _
*)

Inductive locally_sorted : list A -> Prop :=
| nil_locally_sorted : locally_sorted []
| cons1_locally_sorted a : locally_sorted [a]
| consn_locally_sorted a b l : locally_sorted (b::l) -> a <= b -> locally_sorted (a::b::l).

Inductive lelist (a:A) : list A -> Prop :=
    | nil_le : lelist a nil
    | cons_le : forall (b:A) (l:list A), le a b -> lelist a (b :: l).

Inductive sort : list A -> Prop :=
    | nil_sort : sort nil
    | cons_sort :
      forall (a:A) (l:list A), sort l -> lelist a l -> sort (a :: l).

Goal forall l, sort l -> locally_sorted l.
induction l.
  constructor.
  inversion 1; subst.
  destruct l; constructor.
  apply IHl; trivial.
  inversion H3; auto.
Qed.

Goal forall l, lelist

Goal forall l, locally_sorted l -> sort l.
induction 1; constructor.
  constructor.
  constructor.
  assumption.
  inversion IHlocally_sorted; subst.


