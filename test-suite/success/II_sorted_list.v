Require Import Coq.Structures.Orders.

Unset Elimination Schemes.

(** Sorted lists *)

Module SortedLists (Import A : OrderedType).

  Inductive SList : Type :=
  | slist_nil  : SList
  | slist_cons : forall (x : t) (ys : SList), slist_lt x ys -> SList
  with slist_lt : t -> SList -> Type :=
  | slist_lt_triv (x : t) : slist_lt x slist_nil
  | slist_lt_cons (x' x : t) (ys : SList) (p : slist_lt x ys)
    : lt x' x -> slist_lt x' ys -> slist_lt x' (slist_cons x ys p).

  Section elim.
   Variables
    (SListM : SList -> Set)
    (slist_ltM : forall t l, SListM l -> slist_lt t l -> Set)
    (f : SListM slist_nil)
    (f1 : forall (x : t) (ys : SList) (lt : slist_lt x ys) (ys' : SListM ys),
      slist_ltM x ys ys' lt -> SListM (slist_cons x ys lt))
    (f2 : forall x, slist_ltM x slist_nil f (slist_lt_triv x))
    (f3 : forall x' x ys p l q (ys' : SListM ys) (p' : slist_ltM x ys ys' p) (q' : slist_ltM x' ys ys' q),
      slist_ltM x' _ (f1 x ys p ys' p') (slist_lt_cons x' x ys p l q)).

  Definition slist_elim :=
    fix F (c : SList) : SListM c :=
      match c return (SListM c) with
      | slist_nil => f
      | slist_cons x ys l => f1 x ys l (F ys) (F0 x ys l)
      end
    with F0 (x : t) (l : SList) (l' : slist_lt x l) {struct l'} : slist_ltM x l (F l) l' :=
      match l' in slist_lt y v return slist_ltM y v (F v) l' with
     | slist_lt_triv foo => f2 foo
     | slist_lt_cons x' x ys p l q =>
      f3 x' x ys p l q (F ys) (F0 _ _ p) (F0 _ _ q)
    end
    for F.




  (* Simple elimination schemes, not dependent enough *)
  Scheme slist_elim := Induction for SList Sort Type
  with slist_lt_elim := Induction for slist_lt Sort Type.

  Print slist_elim.

End SortedLists.
